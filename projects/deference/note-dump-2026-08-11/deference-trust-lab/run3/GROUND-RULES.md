# Run-3 Ground Rules (read this before doing anything)

*Written 2026-07-01 by the orchestrating session, at Abram Demski's request. This is round 3
of the deference-trust lab. Round 1 lives in `deference-trust-lab/{models,redteam,findings,lean,audit,report}/`,
round 2 in `deference-trust-lab/run2/`. Focus of this round: **legitimacy and deference**.*

## 1. Write boundary — the sandbox contract

You may **create and modify files ONLY inside**:

    deference-trust-lab\run3\

Everything else on this machine is **read-only** for you. In particular you must NOT:

- modify anything in `research\` outside `run3\` (the notes, `li-deference.md`, the v1–v6 docs,
  `anson-notes\`, `lean-deference\`, task-queue files, prior-run folders, etc.);
- run `git add/commit/checkout/clean/reset` or any state-changing git command anywhere;
- run `lake build`, `lake update`, `lake exe cache`, or anything that writes into
  `lean-deference\` or its `.lake\` tree;
- delete or "tidy" any file you did not create this run — files whose names contain
  `(conflict...)` are precious sync artifacts; never touch them;
- write to the user's home directory, temp directories outside your own scratchpad, or any
  other project.

Reading is unrestricted and encouraged: read anything in `research\` you need.

## 2. Lean verification — how to typecheck

A working Lean 4.27.0 + Mathlib environment exists at
`lean-deference\` (build artifacts present;
elan has the pinned toolchain). To typecheck a standalone file you wrote inside `run3\`:

PowerShell:

    Set-Location lean-deference
    lake env lean deference-trust-lab\run3\lean\YourFile.lean

This elaborates your file against the prebuilt Mathlib without writing anything into the
package (the two "local changes" warnings it prints are harmless). Use `import Mathlib` at the
top of your file. Expect ~1–4 minutes per compile (Mathlib olean loading dominates); batch your
edits rather than compiling line-by-line. Never run bare `lean` (no default toolchain is set);
always go through `lake env lean` from the `lean-deference` directory. This exact recipe was
smoke-tested working on 2026-07-01.

**Write STANDALONE files — do not `import LeanDeference` or its modules.** Some of the
package's own `.olean` artifacts are older than their sources (`lake env lean` does not
rebuild), so importing them can silently load stale definitions. If you want to build on a
definition from the existing corpus, copy it into your own file with a comment citing the
source module and line.

Every finished Lean artifact must end with `#print axioms <main theorems>` and the notes must
record the output. Acceptable axioms: `propext`, `Classical.choice`, `Quot.sound`. `sorry` in a
shipped artifact must be declared loudly, never hidden.

## 3. Honesty norms (from rounds 1–2, the hard way)

- **A well-argued negative result, or a refusal, is a valid deliverable.** If you conclude a
  claim is false, a task is misguided, or the honest version is out of reach, say so and show
  why. Never fabricate, never pad, never dress a triviality as a discovery.
- **Hypothesis-laundering ban.** The target object of your claim may not appear as a hypothesis
  of your headline result. "Compiles + sorry-free" is not evidence a claim is real.
- **Shadow test.** For every result, state what the fake version would look like and show yours
  is not it (non-vacuity witnesses, near-misses that must compile, `decide`-checked side
  conditions).
- **Cite prior rounds instead of re-proving them.** `lean-deference\AUDIT.md`, run2's
  `todos\TODOS.md` GLOBAL OFF-LIMITS list, and run2's `report\` define what is already
  established. Re-skinning an established result is duplication, not progress.
- **Interpretation vs. theorem.** Label plainly which parts of a writeup are kernel-checked,
  which are proved on paper, and which are interpretation/slogan.

## 4. Corpus map (where to read)

- `research\li-deference.md` — Abram's human-written master notes (motivation, legitimacy of
  feedback in §0.3, open problems). **The word "legitimacy" in this round means what §0.3
  means: feedback the AI should treat as corrupted vs. legitimate.**
- `research\deference-in-logical-induction-v6.md` — latest integrated note (tower property,
  No-Forced-Trust, the two positive constructions). v2–v5 are earlier strata.
- `research\faithful-acceleration.md`, `research\pointwise-tower-and-faithful-acceleration.md`,
  `research\faithful-acceleration-scope.md` — the acceleration thread (actively edited).
- `research\anson-notes\` — collaborator notes; start at `INDEX.md`.
- `lean-deference\` — the sorry-free Lean corpus backing the notes; `AUDIT.md` is a
  statement-level adversarial audit of exactly what it does and does not verify.
- `research\deference-trust-lab\` (top level = run 1; `run2\`) — prior lab rounds: models,
  red-teams, TODOS, verdicts, reports, critiques. run2's `todos\TODOS.md` has the off-limits
  list and five worked examples of well-specified TODOs; run2's `report\CRITIQUE.md` says what
  the last round actually achieved and where it over-claimed.
- `research\references\logical-induction\main.tex` — the LI paper source (self-trust §4.12 and
  friends, exact theorem statements).
- `research\udt-representation-theorem\` — adjacent project (UDT tiling/representation);
  optional background.

## 5. Layout of this run

    run3\
      GROUND-RULES.md      (this file)
      questions\           phase 1 — proposed research questions, consolidated TODOS.md
      work\<id>\           phase 2 — one folder per TODO: writeups, code, exploratory Lean
      lean\                phase 3 — formalization briefs + final .lean artifacts + notes
      verify\              phase 4a — adversarial faithfulness verdicts per artifact
      critique\            phase 4b — the harsh-referee CRITIQUE.md
      report\              phase 4c — RESEARCH-REPORT.md (the honest headline summary)
