# Setup report — repo scaffolding round

2026-08-10. What was built, what was verified, and what deviated from the
dispatch.

## Awaiting the author

These are stubs in `DECISIONS.md`, repeated here because the dispatch reserved
them:

1. **Visibility and license.** The repository is **private** — inherited from
   its predecessor, not chosen for this scope — and carries no license file.
2. **Whether the leverage frozen trees are registered now** or at the next
   leverage round. `consolidation_aug9/` is registered; nothing else from that
   line is.
3. **Lean library and namespace names.** `Workstudio`, with
   `Workstudio.Delegation.*` and `Workstudio.Leverage.*`, is what the dispatch
   named and what this round built. Renaming is cheap now, expensive after the
   first real development.
4. **Which delegation documents are canonical.** `projects/delegation/notes/` is
   seeded with a pointer, not with documents — see the deviation below.

## Toolchain

| component | version |
|---|---|
| Lean | 4.31.0 (`arm64-apple-darwin24.6.0`, commit `68218e876d2a`) |
| Lake | 5.0.0-src+68218e8 |
| `lean-toolchain` | `leanprover/lean4:v4.31.0` — matched to the dependency's exactly |
| Python | 3.9.6 |

## The pin

| package | rev |
|---|---|
| **agentFoundations** (FAF) | `1fffea44eece253cda1722568a3adfe34e822f03` |
| Foundation | `41d20b5158e9` (transitive) |
| mathlib | `fabf563a7c95` (transitive) |

`1fffea44` is the current `main` of
https://github.com/A-M-Berns/Formalized-Agent-Foundations, and is the commit
whose message is "Bump all pinned dependencies: Lean v4.31.0, upstream
Foundation, vendored upstream ProvabilityLogic" — the unfork that made FAF
pinnable. Only FAF is pinned directly; Mathlib and Foundation arrive through it,
so this repository cannot disagree with its dependency about either.

## Mathlib cache

`lake update` ran the cache fetch itself: **"No files to download"**, then
**8538 already-cached files decompressed** in 11.6s. The machine's Mathlib
oleans were already warm from the FAF work, so nothing was downloaded. A cold
machine will download them; `lake exe cache get` in `lean/` is the command, and
the README says so.

## Build

| step | wall time | result |
|---|---|---|
| `lake update` (fetch + cache) | **1m 22s** | 16 packages resolved |
| `lake build`, first full | **28.7s** | 1714 jobs, green — includes building the Foundation modules the smoke test reaches |
| `lake build`, after adding the two namespace roots | **12.1s** | 1716 jobs, green |

The smoke test's four results and both namespace placeholders audit as required:

```
'Workstudio.Smoke.faf_asympEq_refl'            [propext, Classical.choice, Quot.sound]
'Workstudio.Smoke.faf_substrate_is_encodable'  [propext, Classical.choice, Quot.sound]
'Workstudio.Smoke.mathlib_one_div_tendsto_zero' [propext, Classical.choice, Quot.sound]
'Workstudio.Smoke.chain_compiles'              [propext, Classical.choice, Quot.sound]
'Workstudio.Delegation.namespaceIsLive_holds'  does not depend on any axioms
'Workstudio.Leverage.namespaceIsLive_holds'    does not depend on any axioms
```

**What the smoke test actually certifies.** It reaches three declarations, not
two: `LogicalInduction.AsympEq` and its reflexivity lemma from FAF;
`LogicalInduction.Sentence`'s `Encodable` instance, which is FAF's wrapper over
**Foundation**'s propositional formulas and so exercises that leg of the chain
too; and `tendsto_one_div_add_atTop_nhds_zero_nat` from Mathlib. The last
theorem, `chain_compiles`, states the Mathlib limit in FAF's own `ConvergesTo`
vocabulary, so it typechecks only if both halves of the chain are present and
agree. The declaration names were read out of the pinned sources before use, not
recalled.

## Python

The repo-level runner verifies the frozen digests, enforces the two Lean gates,
and runs each project's runner:

```
FROZEN INPUTS VERIFIED: 3
LEAN SORRY GATE: clean over 3 files
LEAN AXIOM DISCIPLINE: every file carries `#print axioms`
PROJECTS:
  PASS  projects/leverage/workspace
ALL GREEN (1 project(s))
```

The leverage workspace runs 94 tests; the frozen consolidation runs 107 and 180
ledger claims, and is exercised as its own CI job.

## Checksums registered

Three, in `frozen/FROZEN_INPUT_CHECKSUMS.json` with rows in `frozen/MANIFEST.md`:

| name | digest | contents |
|---|---|---|
| `consolidation_aug9/` | `a2ca95ad9d6cafca…` (tree digest) | 59 files |
| `deference-note-dump-2026-06-27.zip` | `bc51a91b84241128…` | 50 files |
| `dose-response-note-dump-2026-07-02.zip` | `a69f8a9876b24dd0…` | 13 files |

Both note dumps existed in several byte-identical copies on the machine; the
copies were checked to be identical before one was registered, and that check is
why the registration names a single canonical digest rather than a choice.

## Deviations from the dispatch

1. **`consolidation_aug9` is registered as an unpacked tree, not an archive.**
   It was already unpacked in the predecessor repository, so it was moved with
   `git mv` — preserving its history and both freeze tags — rather than
   re-imported as a zip. It is registered with a **reproducible tree digest**
   (over sorted relative paths and file digests), and the manifest states the
   recipe. This respects the intake rule that matters — frozen inputs are
   referenced, never edited, and never unpacked *into `projects/`* — while
   keeping it runnable as its own CI job.

2. **`projects/delegation/notes/` is seeded with a pointer, not documents.** The
   dispatch says to seed it with "any documents the author supplies", and none
   were supplied with this round. Candidates exist on the machine — a deference
   paper source, a frozen-deliberation document at v6, a dose-response audit —
   but deciding which are canonical is a naming and provenance decision, which
   convention 6 reserves to the author. Seeding by guess would manufacture
   provenance. Flagged instead.

3. **A `tests/` directory was added at the repo root**, which the dispatch's
   layout did not list. Convention 3 requires a repo-level runner, and it needed
   somewhere to live.

4. **Two namespace root files were added** —
   `Workstudio/Delegation/Basic.lean` and `Workstudio/Leverage/Basic.lean`. The
   dispatch asks for per-line namespaces; git does not track empty directories,
   so without a file the namespaces would have been documentation rather than
   structure. Each holds one trivial declaration and its axiom print, and both
   are in the build.

5. **The repo-level runner does not compile Lean by default.** It runs the
   sorry-free and `#print axioms` gates, which are textual and instant, but
   `lake build` is opt-in behind `WORKSTUDIO_LEAN=1`. A default runner that
   needs a toolchain and a warm cache is a runner people stop running. CI
   likewise does not build Lean; that is a gap, recorded below.

6. **CI has three jobs, not one.** The repo runner, the frozen consolidation's
   own suite, and the leverage workspace's. The latter two predate this round
   and were kept.

## Known gaps

- **CI does not build the Lean.** Doing it properly needs an elan setup step and
  a Mathlib cache restore, which is a real piece of workflow engineering rather
  than a line of YAML; this round left it out rather than adding something that
  would appear to check the Lean and not. Local `lake build` is green and timed
  above.
- **The delegation line has no ledger and no content**, by design: `kernel/` is
  reserved and empty, and the first round supplies both.
- **No license file**, pending the author's decision.
