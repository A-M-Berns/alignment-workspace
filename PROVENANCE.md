# Provenance — repository scaffolding

Two fields per artifact, per `AGENTS.md`: **generator** — who produced it — and
**review status**, `maintainer-reviewed` or `ci-only`. Where the generator is a
model, the model is named; where the prompt author and the executor differ, which
is the normal case for a dispatched round, both are named in *Round attribution*
below.

**Everything in this scaffolding round is `ci-only` unless a maintainer has since
passed over it.** That is not a hedge — it is the accurate label, and the
repository would rather carry an honest one than a flattering one. Flagship
documents may not remain `ci-only`; `README.md`, `AGENTS.md` and
`CONTRIBUTING.md` are the first that need a maintainer's pass.

**Correction, 2026-08-11.** Earlier rows in this file named the executor as
"Claude Opus 4.6". That was wrong; the executor was **Claude Opus 5 (Anthropic)**
throughout, and the rows are corrected below. The prompts for every round were
authored by **Claude Fable 5 (Anthropic)** in maintainer-directed sessions, which
earlier rows did not record at all.

| file or glob | generator | review status | date | round |
|---|---|---|---|---|
| `README.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | `prompts/2026-08-10-repo-scaffolding/` |
| `AGENTS.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `CONTRIBUTING.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `DECISIONS.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — **decisions are the author's; this file records them, and its wording is not the author's** |
| `PRIORITIES.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — items 1–6 restate the frozen consolidation's own list; 7–9 quote the deference audit's §3 by section; 10–11 are proposed by this round |
| `SETUP_REPORT.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same |
| `PROVENANCE.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same |
| `.github/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `tests/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — the gate scripts; their behaviour is checked by CI, their design is not reviewed |
| `lean/lakefile.toml`, `lean/lean-toolchain` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `lean/Workspace/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — the smoke test and the two namespace roots; **machine-checked**: they build and audit to the three standard axioms |
| `projects/*/README.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `projects/leverage/forward/**` | mixed — predates this repository | `ci-only` | — | predates this round; carried over unchanged from the source tree |
| `frozen/**` | **not applicable** | — | — | frozen inputs are third-party or predate this repository; their own provenance is internal to each and their digests are registered in `frozen/MANIFEST.md` |
| `prompts/*/PROMPT*.md` | the maintainer, or a model in a maintainer-directed session | `maintainer-reviewed` — dispatched as written | 2026-08-10 | verbatim as dispatched, including anything they got wrong |
| `prompts/*/REPORT.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same |

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


## Round attribution

| round | prompt author | executor | dates |
|---|---|---|---|
| `2026-08-10-repo-scaffolding` (v1, v2, addendum) | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-10 – 2026-08-11 |
| `2026-08-10-contribution-architecture` | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-licensing-dco-citation` | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-11 |

Rounds predating this repository's provenance discipline — the consolidation and
completing passes now frozen under `frozen/consolidation_aug9/` — have
`executor: unrecorded` rather than a guess. Their prompts were maintainer-supplied
and their reports state what was done; the model that executed them is not
recorded in a form this file can honestly assert.
