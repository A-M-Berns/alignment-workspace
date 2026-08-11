# Setup report — repo scaffolding round (v2)

2026-08-10 / 11. The v2 dispatch superseded a v1 that had already been executed;
both are in `prompts/2026-08-10-repo-scaffolding/`, and this report covers the
delivered state.

## Awaiting the author

1. **License — confirm.** Apache-2.0 is recommended in the dispatch for the
   patent grant. **No license file was written.** A license is a legal grant, the
   dispatch reserves it to the author, and writing an unconfirmed one into a
   repository that may go public is the wrong error to make. Absence means
   default copyright; the README says so plainly rather than leaving a reader to
   guess.
2. **Repository visibility — and it is now load-bearing.** The repository is
   **private**, per the author's instruction. **Branch protection cannot be
   configured**: GitHub refuses it on a private repository on this account's
   plan, returning "Upgrade to GitHub Pro or make this repository public to
   enable this feature." So the contribution model's last enforcement layer is
   pending a decision that was previously only about timing. See below.
3. **NORMATIVE-LEARNER migration** — under `projects/leverage/` or an
   externally-referenced repository. Its consolidation is already here, frozen;
   the question is the live tree.
4. **Namespace names.** `Workstudio`, `Workstudio.Delegation.*`,
   `Workstudio.Leverage.*`. Cheap to change now, expensive later.
5. **Frozen registration beyond the three archives.** Three registered; anything
   else is a decision.

## Toolchain

| component | version |
|---|---|
| Lean | 4.31.0 (`arm64-apple-darwin24.6.0`, commit `68218e876d2a`) |
| Lake | 5.0.0-src+68218e8 |
| `lean-toolchain` | `leanprover/lean4:v4.31.0`, matched to the dependency's |
| Python | 3.9.6 local; `python3` as shipped on `ubuntu-latest` in CI |

## The pin

| package | rev |
|---|---|
| **agentFoundations** (FAF) | `1fffea44eece253cda1722568a3adfe34e822f03` |
| Foundation | `41d20b5158e9` (transitive) |
| mathlib | `fabf563a7c95` (transitive) |

`1fffea44` is the current `main` of Formalized-Agent-Foundations — the commit
"Bump all pinned dependencies: Lean v4.31.0, upstream Foundation, vendored
upstream ProvabilityLogic", the unfork that made it pinnable. **Only FAF is
pinned directly**; Mathlib and Foundation arrive through it, so this repository
cannot disagree with its dependency about either.

## Build and cache

**Locally:** `lake update` 1m 22s, including the cache step, which found the
machine's Mathlib oleans already warm — "No files to download", 8538 files
decompressed in 11.6s. `lake build` 28.7s for 1714 jobs cold, 12.1s after adding
the two namespace roots.

**In CI**, first run, cold `.lake` cache:

| gate | wall time |
|---|---|
| python — project test runners | 8s |
| frozen-integrity — digests and the manifest rule | 5s |
| foundations-verification — the consolidation re-proves itself | 6s |
| **lean — build, sorry-free, axiom audit** | **5m 19s** |
| total run | ~5m 30s (jobs run in parallel) |

The Lean job dominates and that figure is the **cold** one: elan install, `lake
exe cache get`, a full build, then the audit. `actions/cache` keys `lean/.lake`
on `hashFiles('lean/lake-manifest.json', 'lean/lean-toolchain')`, so subsequent
runs restore it and only rebuild what changed. The key changes exactly when the
pin or the toolchain does, which is the right granularity.

## The four gates

1. **python** — `tests/run.py`, which aggregates each project's own runner and
   also runs the textual Lean gates that need no toolchain.
2. **lean** — `lake exe cache get`, `lake build`, then `tests/audit_axioms.py`.
   The audit **re-elaborates every file with `lake env lean`** rather than
   scraping the build log. This is deliberate and it matters: an incremental
   build with nothing to do prints no `#print axioms` output at all, so a
   log-scraping audit would pass silently on an unchanged tree. Re-elaboration
   cannot be fooled that way. The audit fails on any axiom outside
   `[propext, Classical.choice, Quot.sound]`, which is also how `sorryAx` is
   caught, and on any file lacking a `#print axioms` line, and on a
   `#print axioms` that reports nothing — that last case means the declaration
   it names does not exist.
3. **frozen-integrity** — `tests/check_frozen.py` recomputes the tree digest of
   every registered input and fails on drift, on a registered input that has gone
   missing, and on a directory under `frozen/` that is not registered. On a pull
   request it additionally fails any change under `frozen/` unless the same pull
   request updates `MANIFEST.md`; the author's sign-off then happens through
   required review.
4. **foundations-verification** — copies `frozen/consolidation_aug9/` to the
   runner temp directory and runs its own verifier there, then re-runs the
   frozen check to confirm the tree was not modified. Executing from a copy is
   the point: a gate that could mutate frozen content would drift the very digest
   the previous gate defends.

**All four green** on the first run: `31448389113`.

## Foundations-verification result

The frozen consolidation re-proved itself inside CI: retired-name gate clean,
sorry scan clean, **180 ledger claims with statuses agreeing between the theory
parts and the ledger**, every claim-ID family expanded, **26 of its own internal
frozen inputs verified**, 107 tests. So the repository checks two nested layers
of digests — ours over the frozen trees, and the consolidation's own over what it
vendors.

## Checksums registered

Three inputs, each an **extracted tree** rather than an archive, so every claim
is citable by path and line:

| name | tree sha256 | files |
|---|---|---|
| `consolidation_aug9/` | `a2ca95ad9d6cafca…` | 59 |
| `deference-note-dump-2026-06-27/` | `69a23843a69576dc…` | 50 |
| `dose-response-note-dump-2026-07-02/` | `d34afa3ce2888555…` | 13 |

`MANIFEST.md` records for each an archive digest as provenance *and* the tree
digest CI recomputes, plus what cites it, and notes that `consolidation_aug9`
vendors the August 8 consolidation internally. The two note-dump archives were
each present in several byte-identical copies on the machine; they were verified
identical before one was registered.

## Deviations from the dispatch

1. **No `LICENSE` file.** Reserved to the author, and a legal grant is not
   something to guess. Item 1 above.
2. **Branch protection is not configured**, because it is unavailable on a
   private repository on this plan. The full payload is committed at
   `.github/branch-protection.json` with the four exact check names, so applying
   it after the visibility or plan decision is one command:
   `gh api -X PUT /repos/A-M-Berns/alignment-workstudio/branches/main/protection --input .github/branch-protection.json`.
   This was previously a timing question; it is now a gating one, which is why it
   is flagged rather than deferred.
3. **The frozen archives were deleted after extraction.** The dispatch says "no
   zips"; keeping both would have meant two sources of truth. Their digests
   survive in the manifest as provenance.
4. **The note-dump trees were flattened by one level.** Each archive contained a
   single top-level directory repeating its own name; the redundant level was
   removed so paths cite as `frozen/deference-note-dump-2026-06-27/lean/AUDIT.md`
   rather than with the name twice. The tree digest is over the flattened form,
   so it is what CI checks.
5. **`OPEN_PROBLEMS.md` has eleven items, not only the two sources' union.** Six
   come from the consolidation's ranked list, three from the deference audit's
   own §3 "The concerning gaps" — quoted by section, since those are its findings
   and not mine — and two are infrastructure items that are genuinely
   contributable (build the Lean faster in CI; supply necessity witnesses where a
   ledger row lacks one).
6. **Two Lean namespace root files were added.** Git does not track empty
   directories, so without a file the per-line namespaces would have been
   documentation rather than structure. Each holds one trivial declaration and
   its axiom print, and both are in the build and audited.
7. **`CONVENTIONS.md` gained a table saying which conventions are gates and
   which are reviewed.** Four are machine-enforced; five — exact arithmetic, the
   four-part theorem shape, citation integrity, naming, dispatch provenance — are
   review matters. A repository that invites strangers should not blur which is
   which.
8. **`projects/delegation/notes/` is seeded with a pointer, not documents.** No
   documents were supplied with the round. Candidates exist in the frozen
   deference dump — a paper ledger, a frozen-deliberation document at v6, a
   self-referential-settlement-target note — but deciding which are canonical is
   a provenance decision reserved to the author. Seeding by guess would
   manufacture provenance, which convention 5 exists to prevent.

## Known gaps

- **No branch protection yet** — see above. Until it is applied, the gates run
  but do not *block*: a direct push to `main` is possible.
- **The delegation line has no ledger and no content.** `kernel/` is reserved and
  empty; the first round supplies both.
- **The Lean CI cache is unmeasured warm.** The 5m 19s figure is cold. The warm
  figure will appear on the next push that does not change the pin.
