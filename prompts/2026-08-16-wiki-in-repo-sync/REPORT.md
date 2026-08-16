# Report — wiki in the repository, synced outward

**Prompt author:** Claude Fable 5 (Anthropic). **Executor:** Claude Opus 5
(Anthropic). **Dispatched and executed:** 2026-08-16. Write scope granted by the
dispatch.

## What is installed

`wiki/` holds the thirteen pages and `_Sidebar.md` from
`alignment-workspace.wiki.git` at `d86c9d7`, filenames unchanged, plus
`ORIGIN.md` (the intake receipt) and `CONVENTIONS.md`. Tree digest at intake:
`cf260b6f6fe6bb9fcf9497dd7685c28d4134b74e24f3e584457db7acddf504c9` over 14 files.

`.github/workflows/wiki-sync.yml` runs on push to `main` when `wiki/**` changed
and calls `.github/wiki-sync.sh`, which force-pushes `wiki/` to the wiki remote
as one commit naming the source SHA, then re-clones the remote and compares
digests. `.github/wiki_tree_digest.py` is that digest: sha256 over sorted
`<sha256>  <path>` lines.

`checkers/wiki_links.py` requires intra-wiki links to resolve and links into this
repository to carry a 40-hex commit SHA. `wiki/**` is in `tests/path_gate.py`'s
specification enumeration and in `CODEOWNERS`.

## Choices the prompt left open

**`ORIGIN.md` is repo-side only, and so is `CONVENTIONS.md`.** The prompt named
the first as optional; the second follows from *Non-goals*, which forbids new
wiki pages, and a synced `CONVENTIONS.md` would be one. Both are receipts about
the source rather than register content, and neither would read as a page to
someone arriving at the wiki. The exclusion list lives in
`checkers/wiki_links.py` as `REPO_ONLY_FILES` and the sync script reads it from
there, because the two must agree: a file the checker treats as a page and the
sync does not publish is a link that passes CI and 404s for a reader. A self-test
case fails if a name in that tuple stops naming a file.

**No new required check, so `.github/branch-protection.json` is unchanged.** The
new checker runs as two steps inside the existing `checkers` job, whose external
context string is untouched. Giving it a job of its own would have added a
required context, which per `AGENTS.md` may be migrated only after a branch has
emitted it — a two-step dance for a link lint. The job's display name still says
"house harness self-test and the claims registries" and now also runs the wiki
lint; renaming it would change the required context for no gain.

**The sync job's remote is overridable by `WIKI_REMOTE`.** The workflow never
sets it. It exists so the script can be rehearsed against a local bare
repository, which is how the results below were obtained without a token.

## Verification

Full local suite green: `python3 tests/run.py`, plus `python3 tests/path_gate.py
--self-test` and `python3 -m checkers.wiki_links --self-test`. The Lean build was
not run (`WORKSPACE_LEAN` unset); no Lean file changed.

Each new or extended check was shown to fail on a crafted bad input placed in a
real file under `wiki/`, not only in its self-test:

| fixture | result |
|---|---|
| `[the Fixtures page](Fixtures)` appended to `wiki/Home.md` | `WIKI LINKS FAILED: … link to page 'Fixtures', which does not exist in wiki/`, exit 1 |
| a `/blob/main/AGENTS.md` link appended to `wiki/Home.md` | `WIKI LINKS FAILED: … pinned to 'main', not a 40-hex commit SHA`, exit 1 |
| a maintainer's personal name appended to `wiki/Home.md` | `NAME LINT FAILED … wiki/Home.md:65: 'Demski' in prose`, exit 1 |

All three were reverted; the current tree is the imported content plus the one
sentence in *Wiki and lab*.

The path gate's ruling on `wiki/` is tested rather than asserted. `main` mixed
the verdict with where it reads its inputs, so the enumeration had cases and the
ruling on it had none; the verdict is now `rejects(actor, files)` and carries
four cases, including a contributor pull request touching `wiki/Home.md`
(rejected) and a maintainer's (not).

It was also run end to end, against a real one-file diff touching only
`wiki/Roadmap.md`, with the gate reading `GITHUB_BASE_REF` and `GITHUB_ACTOR` as
it does in CI:

```
GITHUB_ACTOR=an-outside-contributor  →  PATH GATE FAILED … - wiki/Roadmap.md      exit 1
GITHUB_ACTOR=A-M-Berns               →  PATH GATE: 1 specification path(s) …      exit 0
```

The same probe run against the gate as it stands on `main` prints "none in the
specification layer" and exits 0, which is the negative control: the rejection
comes from the pattern this round added and not from something already there.

The sync script was rehearsed end to end against a local bare repository seeded
with a stale `Home.md` and an `Obsolete.md` that no longer exists in `wiki/`:

- **Normal run.** 14 files pushed, `Obsolete.md` gone, the web-editor `Home.md`
  replaced, `ORIGIN.md` and `CONVENTIONS.md` absent from the remote, source and
  read-back digests equal, exit 0.
- **Drift between push and read-back.** A third party writes to the remote after
  the push: `WIKI SYNC FAILED: the hosted wiki does not match wiki/ after the
  push`, both digests printed, the extra file named, exit 1.
- **Unreadable remote.** `WIKI SYNC STOPPED: the workflow token could not read
  the wiki remote`, git's message quoted, exit 1.
- **Push refused.** `WIKI SYNC STOPPED: the workflow token was refused push
  access to the wiki remote`, git's `! [remote rejected]` output quoted, exit 1,
  and the message says not to mint a token to get past it.

## The post-sync verification has not been observed

**This is the acceptance criterion the round could not meet, and no rehearsal
substitutes for it.** The job runs on push to `main`; it cannot run before the
change merges, and the round has no merge authority. What the rehearsal
establishes is that the script's success and failure paths behave as described
against a git remote. What it does not establish is that GitHub's ephemeral
`GITHUB_TOKEN` is accepted by `alignment-workspace.wiki.git` — that is a property
of GitHub's permission model on this repository, and nothing available here tests
it. No permanent secret was created and none was requested.

If the token is refused, the job stops with git's exact error and the fallback is
the maintainer's, per the dispatch. It is listed below.

## Deviations

1. **A second *Awaiting the author* stub, beyond the one the prompt names.**
   `AGENTS.md`'s *Security* section says no workflow may be granted a token
   beyond read scope and that raising it is prohibited rather than a maintenance
   decision. The dispatch specifies `contents: write`, and pushing to the wiki
   remote cannot be done with less. The grant is the ephemeral run token on a job
   that triggers only on push to `main`, so it creates no permanent secret and
   nothing a contributor submits reaches it — which satisfies the reason the
   section gives while contradicting the sentence it gives it for. Absorbing that
   silently is the failure `AGENTS.md` §8 names, so it was filed as a stub, as a
   friction entry, and in a comment in the workflow itself. The workflow was
   installed as dispatched. **The maintainer ruled on it during the round** — see
   the addendum, which is why neither the stub nor the friction entry is in the
   tree this pull request ships.

2. **Three documentation edits beyond Deliverable 5's list**, all accuracy rather
   than content: a gates-table row in `AGENTS.md` for the new checker, `wiki/` in
   that file's specification-layer enumeration, and the checker's command in
   `CONTRIBUTING.md`'s local-run block, whose comments name the CI job each
   command belongs to.

3. **Two friction entries filed that the dispatch did not scope**, under the
   §14 obligation. One was the scope conflict above, ruled on and graduated
   before merge. The other — *A generated view of live state lives inside a
   completed round's directory* — stands: `workspace_state --check`
   requires three generated views under
   `prompts/2026-08-13-wikification-and-normativity/` to match what
   `--write-handoff` renders, so filing a `state/rounds.json` entry edits a
   completed round's directory — which `prompts/README.md` says is history and
   not edited. This round did it, via `--write-handoff`; the diff is one row.

4. **`tests/path_gate.py`'s `main` was refactored**, not only extended: the
   verdict moved into `rejects()` so Deliverable 4's confirmation could be a test
   rather than a claim. Behaviour is unchanged and the existing cases still pass.
   This is a trust-chain file.

5. **`tests/name_lint.py` needed no scope change.** It reads `git ls-files
   '*.md'` and excludes `prompts/` and the consolidated trees, so `wiki/` was in
   scope the moment the files were tracked. Extending coverage therefore meant
   pinning it: three self-test cases assert that wiki pages appear in the scanned
   set, that a name inside `wiki/Home.md` is caught, and that no exclusion
   prefix covers `wiki/`. Reporting this as a code change would misdescribe what
   protects the coverage.

## What this does not establish

The token question above is the largest. Beyond it:

- **Nothing checks that a page says something true.** The link checker checks
  that a link resolves and that a repository link is pinned. Whether the pinned
  commit contains what the sentence claims it contains is unchecked, and
  `AGENTS.md` already records citation integrity as ungated in general.
- **The volatile-quantity rule is prose only.** `wiki/CONVENTIONS.md` states it;
  `PRIORITIES.md` item 37 is the checker; nothing enforces it today. The current
  pages were read for links and personal names, not audited for volatile
  numbers — that audit belongs to the content round the dispatch defers.
- **`checkers/` has no coverage check.** `tests/run.py` fails if a script in
  `tests/` is never invoked; there is no equivalent for `checkers/`, so a future
  edit could unwire `wiki_links` from the suite without anything reporting it.
  Not filed: the exposure is one line in two files, and adding a second coverage
  mechanism is a design decision, not a repair.
- **The hosted wiki's history is not in this repository.** No grafting was
  attempted; `wiki/ORIGIN.md` is the provenance record in its place, and the
  first sync force-pushes over that history rather than continuing it.
- **The pages' content is unchanged and unreviewed by this round.** One sentence
  was added to `Home.md`'s *Wiki and lab* section. Nothing else was read for
  correctness, and the pages remain `ci-only`.

## Filed

- `PRIORITIES.md` item 36 — this round's own demand item, marked answered by it.
- `PRIORITIES.md` item 37 — the volatile-state consistency checker for `wiki/`,
  open and dispatchable.
- `PRIORITIES.md` item 38 — a check enforcing the write-scope conditions and the
  job enumeration, filed on the maintainer's ruling below.
- `PRIORITIES.md` *A generated view of live state lives inside a completed
  round's directory* — the friction entry that stands.
- `DECISIONS.md` — two dated entries, and one *Awaiting the author* stub.

Empty findings, reported as empty: no page in `wiki/` had a dangling link, an
unpinned repository link, or a personal name in prose at intake. The checkers
found nothing to fix, which is why every one of them was shown failing on a
crafted input before being believed.

## Outstanding maintainer actions

1. **Merge this branch to `main` and read the `wiki-sync` job's log.** The job
   prints the source digest, the read-back digest, and either
   `WIKI SYNC: hosted wiki matches wiki/ at <sha>` or a `STOPPED`/`FAILED` block
   with git's exact error. This is the acceptance criterion the round could not
   check.
2. **If the token is refused, decide the fallback.** Do not add a personal access
   token to make the job pass; the choice is between publishing the wiki by hand
   and dropping the outward sync. The write-scope question itself is settled —
   `DECISIONS.md`, 2026-08-16 — and a refusal is about what the token can reach,
   not about what the constitution permits.
3. **Decide the identity a wiki pull request is opened under** — `DECISIONS.md`,
   *Awaiting the author*. Until then, only a pull request whose `GITHUB_ACTOR` is
   in `MAINTAINERS` can touch `wiki/` and pass `path-gate`.
4. **Confirm `wiki/**`'s path-gate entry**, as the deck's entry was confirmed:
   this round added a pattern to `tests/path_gate.py`, a trust-chain file. The
   dispatch scoped it, so it is not flagged as an overreach — it is listed
   because a specification-enumeration change is a maintainer's to hold.

## Addendum — the write-scope ruling, 2026-08-16

The maintainer ruled on deviation 1 while the pull request was open, before
merge: amend *Security*. `AGENTS.md` now separates the absolute rule — no stored
credential, anywhere — from what a job's run token may do, and permits write
scope under four conditions, with the jobs holding it enumerated by name. The
dated entry is in `DECISIONS.md`; the stub left *Awaiting the author* and the
friction entry left *Workspace friction*, both as those sections prescribe.

The amendment turned an absolute prohibition into a conditional permission, and
a condition nothing reads is the failure this repository has already paid for:
the residue sweep reported clean while `README.md`'s third line violated a
standing decision, which is why the naming rule became a lint. So on the
maintainer's instruction the check was written in the same round —
`tests/workflow_scope.py`, item 38, answered.

**What it checks.** Conditions 1, 3 and 4 over every workflow: a write-granting
job triggers on `push` restricted to a protected branch and never on
`pull_request` or `pull_request_target`; no workflow names any secret but
`GITHUB_TOKEN`; and no workflow's top-level `permissions:` grants write, so a job
added beside an existing one inherits nothing. Plus both of the enumeration's
failure directions: a write grant absent from it, and an entry naming a job no
workflow defines. The enumeration is read from `write-scope` markers in
`AGENTS.md` rather than copied into the gate, so the list a reader sees is the
list the gate enforces.

**What it does not check.** Condition 2 — publishes rather than adjudicates — in
the one form a script can see: that a write-granting job's context is not a
required check, so nothing merges on its verdict. That no registry or protected
setting is downstream of what such a job *writes* is not machine-readable, and
both `AGENTS.md` and the item say so rather than implying otherwise. The parse is
line-oriented, since YAML is not in the standard library; it understands the
indentation these workflows are written in and would need extending for a form
they do not use. It is `.github/workflows/*.yml` only — a workflow living
elsewhere is invisible to it, and GitHub reads none.

Beyond its twenty-one self-test cases, the gate was run against the real
`wiki-sync.yml` mutated five ways, each reverted:

| mutation | result |
|---|---|
| `pull_request:` added to its triggers | `job 'wiki-sync' grants write scope in a workflow triggered by ['pull_request'] — reachable by what a contributor submits` |
| the grant moved to the workflow default | `the workflow's default permissions: grants write` |
| `secrets.GITHUB_TOKEN` → `secrets.WIKI_DEPLOY_PAT` | `names stored secret(s) ['WIKI_DEPLOY_PAT']` |
| the job renamed to `publisher` | `job 'publisher' grants write scope and is not named in AGENTS.md's Security section` |
| the `write-scope` marker deleted from `AGENTS.md` | `AGENTS.md declares no write-scope entries … a missing marker is a lost grant, not an empty one` |

It runs in the `python` job, so no required-check identity changed and
`.github/branch-protection.json` is still untouched.

The ruling was taken as a maintainer act on a trust-chain document, which
`AGENTS.md` reserves to the maintainer and which self-review satisfies, with the
ledger entry as the review record. The wording of the amendment and the gate are
this round's and are `ci-only`; the decision they record is not.
