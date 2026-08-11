# ALIGNMENT-WORKSTUDIO — repo scaffolding round

*Dispatched 2026-08-10. Kept verbatim as sent, per `prompts/README.md`.*

---

You are setting up **alignment-workstudio**: the working monorepo for the
Berns–Demski research program. It will hold multiple research lines (initially
**leverage** — the normativity/answerability program — and **delegation** — the
deference/corrigibility program), with exact-arithmetic Python model work per line and
a single shared Lean 4 project that formalizes against **Formalized-Agent-Foundations
(FAF)** as a pinned dependency (https://github.com/A-M-Berns/Formalized-Agent-Foundations;
the recent dependency bump / Foundation unfork was done to make FAF pinnable — build
against its current main).

The repo may start from the author's existing local repo (initial name "normative
learning") — if so, rename/repoint rather than recreate, preserving any history.

## Layout to create

```
alignment-workstudio/
  README.md
  CONVENTIONS.md
  DECISIONS.md
  projects/
    leverage/
      README.md          ← pointer: authoritative frozen trees live in frozen/;
                           new leverage rounds land here
    delegation/
      README.md          ← the deference/corrigibility line; arc + ledger pointers
      kernel/            ← empty; reserved for the finite delegation kernel round
      notes/             ← seeded with any documents the author supplies
                           (paper ledger, triangle-compatibility statement, prompts
                           awaiting dispatch)
  lean/                  ← ONE Lake project (see below)
  frozen/
    MANIFEST.md
    FROZEN_INPUT_CHECKSUMS.json
  prompts/
    README.md            ← the dispatch convention (below)
```

## Lean project (the part to get exactly right)

- One Lake project in `lean/`, library name `Workstudio`, with per-line namespaces:
  `Workstudio.Delegation.*`, `Workstudio.Leverage.*`.
- **FAF as a pinned git dependency**, pinned to a specific commit hash (record it in
  SETUP_REPORT.md and DECISIONS.md). Match `lean-toolchain` to FAF's exactly. Fetch
  Mathlib oleans via `lake exe cache get` before building.
- A smoke-test file `Workstudio/Smoke.lean` that imports at least one real
  declaration from FAF and one from Mathlib and proves a trivial lemma using each —
  the point is to certify the dependency chain compiles, not to do mathematics.
- `lake build` must finish green; report wall time.
- House Lean discipline (record in CONVENTIONS.md): sorry-free gate; every file ends
  with `#print axioms` lines; results must audit to `[propext, Classical.choice,
  Quot.sound]`; external theory (LI paper facts, corpus results) enters only as
  named hypotheses, never re-asserted as axioms.

## CONVENTIONS.md (write it; these are the house standards, not suggestions)

1. Exact arithmetic in all theorem-bearing Python (`fractions.Fraction`; floats only
   in clearly-marked visualization/exploration code).
2. Every theorem ships as: statement (in a THEOREMS.md or docstring) + implementation
   + test + a necessity witness for each hypothesis where feasible.
3. One-command test runner per project; one repo-level runner that runs them all.
4. Frozen inputs are immutable: anything in `frozen/` is read-only, checksummed in
   FROZEN_INPUT_CHECKSUMS.json, and referenced — never edited.
5. Citation integrity: no unverified identifiers — cite content inline or against a
   checksummed frozen tree; never a remembered label.
6. Agent rounds flag naming decisions for the author; agents do not coin permanent
   names.
7. Dispatch provenance: every agent round's prompt and report live under
   `prompts/YYYY-MM-DD-round-name/` (PROMPT.md + REPORT.md + any decision items),
   committed with the work.

## frozen/ intake

Checksum and register whatever archives the author supplies at dispatch time
(expected candidates: consolidation_aug9, the deference note dump 2026-06-27, the
dose-response note dump 2026-07-02). MANIFEST.md gets one entry per archive: name,
date, sha256, one-line description, and what cites it. Do not unpack into projects/;
projects reference frozen trees by path.

## README.md (top level)

Short. What the repo is (the working monorepo for the research program: models,
proofs, and dispatch provenance for the leverage and delegation lines, formalized
against FAF), the layout, how to run tests, how to build the Lean, and the
one-paragraph description of each line with a pointer into projects/. No research
content in the README — it points, it doesn't contain.

## DECISIONS.md

Seed it as a dated decision ledger, initial entries: repo name and scope decided
2026-08-10; FAF pinned at commit <hash>; single-Lake-project structure; the
conventions above. Leave author-pending entries as explicit stubs: repo visibility /
license; whether leverage frozen trees are registered now or at the next leverage
round; final Lean namespace names if the author wants different ones.

## Deliverables

- The repo, building and testing green (Lean smoke test + an empty-but-wired Python
  test runner).
- SETUP_REPORT.md at repo root: toolchain versions, FAF pin, Mathlib cache status,
  build times, checksums registered, anything that deviated from this prompt and why.
- The author-pending stubs in DECISIONS.md listed at the top of the report.

## Reserved to the author (flag, do not decide)

- Visibility/license.
- Whether to register the leverage frozen trees now.
- Any renaming of the `Workstudio` library or namespaces.
