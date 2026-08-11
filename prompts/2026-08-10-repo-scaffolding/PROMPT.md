# ALIGNMENT-WORKSTUDIO — repo scaffolding round (v2: public, CI-enforced)

*Dispatched 2026-08-10. Kept verbatim as sent, per `prompts/README.md`. This v2
superseded a v1 that had already been executed; the v1 dispatch is kept beside
this file as `PROMPT-v1-superseded.md`, and the delivered state is v2's.*

---

You are setting up **alignment-workstudio**: the public working monorepo for the
Berns–Demski research program. Two research lines initially — **leverage** (the
normativity/answerability program) and **delegation** (the deference/corrigibility
program) — with exact-arithmetic Python model work per line and one shared Lean 4
project formalizing against **Formalized-Agent-Foundations (FAF)** as a pinned
dependency (https://github.com/A-M-Berns/Formalized-Agent-Foundations; recently
unforked/bumped precisely to be pinnable).

Design intent, which should shape every choice: **anyone can contribute, and quality
is enforced by machine-checkable gates, not by trust.** The program's house
discipline (exact rationals, theorem = code + test + witness, sorry-free Lean with
axiom audits, checksummed frozen inputs, one-command verifiers) is exactly what
makes external contribution adjudicable by CI. Build the repo so that a stranger's
PR is either verifiably correct or automatically rejected.

The repo may start from the author's existing local repo (initial name "normative
learning") — rename/repoint rather than recreate, preserving history.

## Layout

```
alignment-workstudio/
  README.md                ← public-facing orientation (see below)
  CONTRIBUTING.md
  CONVENTIONS.md
  DECISIONS.md
  OPEN_PROBLEMS.md         ← the contribution funnel (see below)
  LICENSE                  ← Apache-2.0 recommended; AUTHOR CONFIRMS
  .github/
    workflows/ci.yml       ← the four gates (below)
    PULL_REQUEST_TEMPLATE.md
    CODEOWNERS             ← the author owns everything initially
  projects/
    leverage/
      README.md            ← what the line is; frozen foundations live in frozen/;
                             forward rounds land here as dated directories
    delegation/
      README.md            ← the line's arc; pointers to the paper ledger
      kernel/              ← reserved for the finite delegation kernel round
      notes/               ← seeded with author-supplied docs (paper ledger,
                             triangle-compatibility statement, pending prompts)
  lean/                    ← ONE Lake project (below)
  frozen/
    MANIFEST.md
    FROZEN_INPUT_CHECKSUMS.json
    consolidation_aug9/    ← EXTRACTED TREE (not a zip), author-supplied
    deference-note-dump-2026-06-27/
    dose-response-note-dump-2026-07-02/
  prompts/
    README.md              ← dispatch-provenance convention
```

## Lean project

- One Lake project in `lean/`, library `Workstudio`, namespaces
  `Workstudio.Delegation.*` and `Workstudio.Leverage.*`.
- FAF pinned by commit hash (record in SETUP_REPORT.md and DECISIONS.md);
  `lean-toolchain` matched to FAF's; Mathlib oleans via `lake exe cache get`.
- Smoke test `Workstudio/Smoke.lean` importing ≥1 real declaration from FAF and ≥1
  from Mathlib, proving a trivial lemma with each — certifies the dependency chain.
- House discipline (goes in CONVENTIONS.md and is CI-enforced): sorry-free; every
  file ends with `#print axioms`; results audit to
  `[propext, Classical.choice, Quot.sound]` only; external theory (LI paper facts,
  corpus results) enters as named hypotheses, never asserted as axioms.

## CI (.github/workflows/ci.yml) — the four gates

1. **python**: repo-level test runner green (it aggregates per-project runners).
2. **lean**: `lake build` green with the Mathlib cache and a GitHub Actions cache of
   `.lake/` so CI time is tolerable; then an axiom-audit script that extracts every
   `#print axioms` result and fails on anything outside the allowed three (this also
   catches `sorryAx`).
3. **frozen-integrity**: recompute sha256 over `frozen/` and diff against
   FROZEN_INPUT_CHECKSUMS.json; fail on drift. Additionally fail any PR that
   modifies files under `frozen/` unless the same PR updates MANIFEST.md (the
   author's sign-off then happens via required review).
4. **foundations-verification**: run the frozen consolidation's own one-command
   verifier from inside `frozen/consolidation_aug9/` (read-only execution; copy to
   a temp dir if its runner writes anything). The repo thereby continuously
   re-proves its foundations on every push.

Branch protection on main: PRs only, all four gates required, author review
required. Note in SETUP_REPORT.md the measured CI wall time and the caching setup.

## CONTRIBUTING.md + PR template

CONTRIBUTING.md, short and concrete: how to run everything locally (the same four
gates); what a contribution must contain (for a theorem: statement + implementation
+ test + necessity witnesses where feasible; for Lean: builds, audits clean; for a
witness: the exact instance and the check that verifies it); where to find work
(OPEN_PROBLEMS.md); the two hard rules — nothing in `frozen/` changes, and
contributors do not coin permanent names (naming decisions are the author's; flag
proposals in the PR).

PULL_REQUEST_TEMPLATE.md fields: which OPEN_PROBLEMS/ledger item this addresses;
which tests/checks cover it; **new names introduced** (may be "none"); anything the
author must decide.

## OPEN_PROBLEMS.md

Seed from author-supplied material (the delegation paper ledger's open items and the
consolidation's OPEN_PROBLEMS.md), formatted as contributable units: one item = a
precise statement, its context pointer (path into frozen/ or projects/), what a
solution must ship (per CONTRIBUTING.md), and a difficulty tag. This file is the
source of truth; GitHub issues mirror it, not the reverse.

## frozen/ intake

Author supplies the archives at dispatch time. For each: extract to a directory
(browsable and citable by path — no zips), register in MANIFEST.md (name, date,
sha256 of the archive AND a tree-hash of the extracted content, one-line
description, what cites it), and add to FROZEN_INPUT_CHECKSUMS.json. Expected:
consolidation_aug9 (which vendors consolidation_aug8 internally — note that in the
manifest), the deference note dump 2026-06-27, the dose-response note dump
2026-07-02. Do not unpack frozen content into projects/; projects cite by path.

## README.md (top level, public-facing)

Orient a stranger in one screen: what the program is (one paragraph per line, plain
register — the FOR_HUMANS culture applied at repo level); the layout; the
one-command verification story ("clone, run these two commands, and every claim in
this repository is re-checked in front of you"); how to contribute (pointer);
license. No research content — it points.

## DECISIONS.md

Dated ledger, seeded: repo name/scope (2026-08-10); public + CI-enforced
contribution model; FAF pin at commit <hash>; single-Lake-project structure; frozen
immutability rule; license (pending author confirm). Author-pending stubs listed at
top: license confirm; whether NORMATIVE-LEARNER migrates under projects/leverage/ or
remains an externally-referenced repo; frozen-tree registration timing for anything
beyond the three expected archives; namespace renames if any.

## Deliverables

- The repo, all four CI gates green on main, branch protection configured.
- SETUP_REPORT.md: toolchain versions, FAF pin, cache setup and CI wall times,
  checksums registered, foundations-verification result, deviations from this
  prompt and why, and the author-pending decision list at the top.

## Reserved to the author (flag, do not decide)

- License (Apache-2.0 recommended for the patent grant; docs could carry CC-BY 4.0
  if split licensing is wanted — simplest is one license).
- NORMATIVE-LEARNER migration (in vs. referenced).
- Any renaming of the `Workstudio` library or namespaces.
- Repo visibility timing (scaffold works identically private-first, public later).
