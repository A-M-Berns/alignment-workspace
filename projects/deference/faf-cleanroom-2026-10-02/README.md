# faf-cleanroom — a clean-room formalization run over FAF

Lean 4 formalizations of a research corpus on logical induction, deference,
corrigibility, decision theory and Bayesian logical induction (BLI), stated over
[Formalized Agent Foundations](https://github.com/A-M-Berns/Formalized-Agent-Foundations)
(FAF) and adversarially audited, 2026-09-29 to 2026-10-02. **Start with
[`DIGEST.md`](DIGEST.md).** Status and provenance are in [`ORIGIN.md`](ORIGIN.md).

**Register.** Everything here is AI-generated (Claude Fable 5.1 agents) and has
not been vetted by the author. Kernel-checked means the proof is a proof of the
statement as written; whether the statement is the claim is what each package's
audits judge, and they are AI judgments too.

## This tree is not built by this repository's CI

The repository's `lean` job builds `lean/**` only, within a 25-minute budget,
against FAF `c0d885b`. This library is pinned to FAF `159ec3f` (309 commits
newer) and takes hours to build, so it is published here as a consolidated tree
with local verification instructions, not as proof-layer contributions. Moving
selected results into `lean/` needs a FAF pin bump there and is future work.

## Verify it yourself

From this directory, with [elan](https://github.com/leanprover/elan) installed
(the toolchain is pinned in `lean-toolchain`, Lean v4.31.0):

```bash
lake exe cache get                 # Mathlib oleans
lake build +Cleanroom              # the aggregator: every module but one (below)
python3 scripts/audit.py --no-replay $(sed -n 's/^import //p' Cleanroom.lean | tr '\n' ' ')
```

The audit takes the root modules listed in `Cleanroom.lean` plus everything they
import. Building FAF and the library from scratch takes several hours and about
5 GB of memory for the heaviest modules. `lake build` (no target) also builds
`Cleanroom/Corrigibility/CorrLegitGeneral/WitnessesMutual.lean`, which no
package root imports and which needs more than 4.8 GB to elaborate; the package
discloses it as not landed.

## Mechanical state at intake (2026-10-02)

- **Build:** `lake build +Cleanroom` succeeded — 1,790 modules in one
  environment, so no two packages define the same name — and again on these
  exact files after the intake's one rename (`bli-trajectory`'s `JournalResponse`,
  see `ORIGIN.md`), with the gate passing.
- **Gate** (`scripts/audit.py --no-replay` over those 1,790 modules): 69,662
  declarations; axioms used: `propext`, `Classical.choice`, `Quot.sound`, and
  `sorryAx` only through the 178 open statements listed in `OPEN.txt`;
  0 unlisted `sorry`, 0 `native_decide`, 0 stale open-list entries. **Lint: 6
  failures**, all `local macro` tactic shorthands for `simp` calls inside proofs
  in `Cleanroom/Decision/DpCalibLimits/` (they only produce proof terms, which
  the kernel checks, so they cannot change what a statement means, but the run's
  standards forbid custom syntax).
- **Kernel replay** (`leanchecker`, in dependency-ordered batches, run on the working tree): at intake **818 of 1,675 modules replayed, all passed, 0 failed**; the 115 package-root modules, which declare nothing of their own, are covered by their submodules' replays. The replay continues; its final count will be appended to this file.
  **Final (2026-10-02 22:16 EDT): all 1,675 modules that declare anything replayed and passed, 0 failed.**
- **Audits:** 106 work packages; **83 passed** both final adversarial audits
  (statement fidelity; attempted breakage), **23 ended flagged** with blocking
  issues still open after their last round — 11 about the shape of a Lean
  statement, 12 about prose or labels only; none is a false theorem. Each
  package's status is in its `packages/<key>/<key>-report.md` and in
  `DIGEST.md` §5.
- **Clean room:** no agent of the run opened the earlier run's files or
  transcripts (checked over every agent's tool calls).

## What was not shown

- That the statements are the claims of the source documents: that is the
  audits' judgment, not the kernel's, and some packages are flagged.
- Anything conditional on an open statement (`OPEN.txt`) or on a disclosed
  `(b)`/`(c)` hypothesis (each headline's docstring and ledger row says which).
- Comparison with the earlier independent run.
- Vetting by the author of any result.

## Layout

| path | contents |
|---|---|
| `Cleanroom/<Area>/<Package>/` | Lean, namespace `Cleanroom.<Area>.<Package>` |
| `packages/<key>/` | `<key>-report.md`, `-findings.md` (defects found in the sources), `-ledger.md`, `-open.txt`, final-round audits and their probe files; dual packages also `attempt-a/`, `attempt-b/` |
| `sources/` | cited source documents, paths as in the author's research tree |
| `LEDGER.md` | all packages' ledgers in one file |
