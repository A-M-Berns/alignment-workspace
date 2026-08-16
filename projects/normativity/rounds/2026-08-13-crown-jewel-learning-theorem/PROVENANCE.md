# Provenance

Every file in this directory:

- **generator** — `prompts/2026-08-13-crown-jewel-learning-theorem/`, executed by
  Claude Opus 5 (Anthropic) against a dispatch written by GPT-5.6 Sol (OpenAI)
- **review status** — `ci-only`
- **date** — 2026-08-13

| path | notes |
|---|---|
| `README.md` | |
| `CROWN_JEWEL_THEOREM.md` | the round's central artifact |
| `ASSUMPTION_AUDIT.md` | |
| `COVERAGE_INTERFACE.md` | |
| `REPAIR_LANGUAGE.md` | |
| `LEARNING_DYNAMICS.md` | corrected by the refinement pass; the coherence inference is withdrawn |
| `COMPILER_SOUNDNESS.md` | refinement pass; verdict corrected by the final pass |
| `INTERFACES.md` | final pass |
| `THEOREM_STRENGTH_LADDER.md` | |
| `PROSECUTION.md` | |
| `PATH_INVENTORY.md` | |
| `src/*.py` | imports the two merged rounds and the item-30 learner by path; copies neither |
| `tests/*.py` | |

The Blum–Mansour source audit is not repeated here; it is the merged round's
`SOURCE_AUDIT.md` and nothing in this round depends on a point it did not check.

The retired `FOR_HUMANS.md` remains in git history; its maintained successor is
the [Normative Response Learning wiki](https://github.com/A-M-Berns/alignment-workspace/wiki/Normative-Response-Learning).

`lean/Workspace/Normativity/Contrib/SurgicalRepairBound.lean` carries the same
generator and review status; it is listed in the Lean contrib provenance file.

No originating chat bundle.
