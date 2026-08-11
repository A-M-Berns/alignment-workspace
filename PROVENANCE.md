# Provenance — repository scaffolding

Origin classes per `AGENTS.md`: `human` (author-written), `llm-reviewed`
(LLM-generated, author has passed over it and stands behind it),
`llm-unreviewed` (LLM-generated, not yet author-reviewed).

**Everything in this scaffolding round is `llm-unreviewed` unless the author has
since passed over it.** That is not a hedge — it is the accurate label, and the
repository would rather carry an honest one than a flattering one. Headline
documents may not remain in this state; `README.md`, `AGENTS.md` and
`CONTRIBUTING.md` are the first that need the author's pass.

| file or glob | class | generator | date | round |
|---|---|---|---|---|
| `README.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | `prompts/2026-08-10-repo-scaffolding/` |
| `AGENTS.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same |
| `CONTRIBUTING.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same |
| `DECISIONS.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same — **decisions are the author's; this file records them, and its wording is not the author's** |
| `OPEN_PROBLEMS.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same — items 1–6 restate the frozen consolidation's own list; 7–9 quote the deference audit's §3 by section; 10–11 are proposed by this round |
| `SETUP_REPORT.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-11 | same |
| `PROVENANCE.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-11 | same |
| `.github/**` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same |
| `tests/**` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same — the gate scripts; their behaviour is checked by CI, their design is not reviewed |
| `lean/lakefile.toml`, `lean/lean-toolchain` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same |
| `lean/Workstudio/**` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same — the smoke test and the two namespace roots; **machine-checked**: they build and audit to the three standard axioms |
| `projects/*/README.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-10 | same |
| `projects/leverage/workspace/**` | mixed | — | — | predates this round; carried over unchanged from the source tree |
| `frozen/**` | **not applicable** | — | — | frozen inputs are third-party or predate this repository; their own provenance is internal to each and their digests are registered in `frozen/MANIFEST.md` |
| `prompts/*/PROMPT*.md` | `human` | the author | 2026-08-10 | verbatim as dispatched, including anything they got wrong |
| `prompts/*/REPORT.md` | `llm-unreviewed` | Claude Opus 4.6 | 2026-08-11 | same |

## No originating chat bundle

The chat-bundle pointer is optional and none exists for this round: no dump has
been requested or assembled. If one is later produced for this work, it enters
`frozen/` under the release gate in `AGENTS.md` and this table gains the pointer.

## What "machine-checked" does and does not cover here

The Lean files are machine-checked in the strong sense: they compile and their
axiom audit is clean. The gate scripts are machine-*exercised* — CI runs them and
they pass — but that is evidence they run, not that they check the right thing.
Nobody but their generator has yet read them with an eye to whether the rule they
implement is the rule intended. That is a review item, and it is exactly the kind
of thing this file exists to make visible.
