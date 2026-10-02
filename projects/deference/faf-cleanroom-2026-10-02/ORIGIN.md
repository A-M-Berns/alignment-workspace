# Origin — the faf-cleanroom formalization run, 2026-10-02

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

The output of a multi-agent formalization run, 2026-09-29 to 2026-10-02: Lean 4
formalizations, over Formalized Agent Foundations (FAF), of a maintainer's
research corpus on logical induction, deference, corrigibility, decision theory
and Bayesian logical induction, with the run's adversarial audits and the human
source documents the formalizations cite. **Everything here is AI-generated and
has not been vetted by the author** except where a source document records the
author's own words. In these files **the author** is that maintainer and **the
co-maintainer** is the other maintainer; **AUTHOR** marks the author's words in
quoted dialogue.

The run is a *clean room*: an earlier, independent formalization run of the
same corpus exists, and no agent of this run read it, so that the two can be
compared as independent attempts. That comparison has not been done.

| path | what it is |
|---|---|
| `README.md` | how to verify, the run's mechanical state, what was not shown |
| `DIGEST.md` | the entry point: headline results, the Bayesian-logical-induction agenda, corrections to the corpus, flagged packages, open statements |
| `STANDARDS.md` | the quality bar every package was audited against |
| `LEDGER.md` | one row per headline declaration: source, claim, kind, fidelity, hypotheses, witness, status |
| `OPEN.txt` | the 178 declarations deliberately stated with `sorry` (open statements), each with its reason |
| `Cleanroom/`, `Cleanroom.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` | the Lean library: 1,791 files, one directory per work package |
| `scripts/audit.py` | the trust gate (axiom audit, open-list check, source lint, optional kernel replay) |
| `packages/<key>/` | per work package: report, findings about the sources, ledger, open list, and the final audit round (two lenses) with its probe files |
| `sources/` | the cited source documents that are not already published elsewhere, as vetted for release (see *Intake deltas*) |

## As received

| | |
|---|---|
| received | 2026-10-02 |
| archive sha256 | n/a — assembled in-repo from the run's working tree, never an archive |
| tree sha256 at intake | `cce2ea462aa655dd1921e42e7f3a2a17b3fc05d96e8351003131f32082a98e73` (sha256 of the sorted `sha256sum` listing of every file except this one) |
| files at intake | 3284 |
| generator | work packages by Claude Fable 5.1 (Anthropic) agents; orchestration and intake by Claude Opus 5.5 (Anthropic); pre-release vetting by Claude Sonnet 5.5 (Anthropic) agents |
| FAF pin | `159ec3f4d55948d741302a915cce388616a3875f` (this repository's `lean/` pins `c0d885b`; see `README.md`) |

## Intake deltas — what differs from the working files

- **Selection.** Each package's mandates, earlier audit rounds and handoffs, the
  run's surveys, plans, prompts and orchestration logs are not included; the
  final audit round of each package is. Published papers the run cites are not
  redistributed; source documents already in this repository (the note dumps
  under `projects/`) are cited there rather than copied.
- **Naming.** The author's name is replaced by *the author* throughout the
  Markdown, the co-maintainer's by *the co-maintainer*, and speaker labels by
  AUTHOR. Other researchers keep their names where their work or ideas are
  cited (among them Sam Eisenstat, Martín Soto — whose 2023 notes are included
  with permission — and AISC 2025 participants). Lean docstrings and file names
  are unchanged, so some cite the author by name (for example in the title of a
  Soto note).
- **Links.** Obsidian `[[wikilinks]]` became ordinary relative Markdown links
  where the target is in this tree, and backticked names where it is not.
  Working-tree paths (`run/wp/<key>/`) became `packages/<key>/`; machine paths
  were removed.
- **Scrubbing.** Personal identifiers and logistics, personal-life passages and
  candid assessments of third parties were cut and marked `[scrubbed]` by
  agents before the author's review. By the author's rulings at intake: quotes
  of private correspondence with third parties (an August 2026 email thread, a
  September 2026 email thread whose other participants are referred to as
  *[another person in the thread]*, private Discord messages) were cut, with
  the author's own emails and the technical analysis kept; one file of AI notes
  planning a reply to such correspondence was removed; mentions of restricted
  audio recordings were removed (one idea drawn from an AI summary of a
  conversation is attributed to its originator with a flag that the summary
  may misrepresent their view); positions of a colleague summarized from a private
  debate were cut; and AI-written first-person reconstructions of named
  researchers' views were removed, with the responses to them kept and their
  attribution neutralized.
- **Attribution correction.** The `bli-trajectory` package's argument from the
  author's 2023 journal was named after two researchers whose actual proposals
  the notes do not record accurately. It is renamed (module `JournalResponse`,
  declarations `journalResponse_*`) and carries a disclaimer; the two journal
  pages carry an intake note.
- **Lean.** No Lean file was edited at intake except that rename and its
  docstrings (`Cleanroom/Bli/BliTrajectory/JournalResponse.lean`, formerly
  `ScottBenja.lean`, and the import in `Cleanroom/Bli/BliTrajectory.lean`);
  the library was rebuilt and re-gated after it (see `README.md`).
