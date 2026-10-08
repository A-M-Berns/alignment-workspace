# Origin — the `corr-value-change` package of the faf-cleanroom run, 2026-10-07

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

One work package, run on 2026-10-07 under the standards and tooling of the
clean-room formalization run published as
[`faf-cleanroom-2026-10-02`](../faf-cleanroom-2026-10-02/ORIGIN.md): a Lean 4
formalization, over Formalized Agent Foundations (FAF) `159ec3f`, of the note
[value-change-as-epistemic-update](../corrigibility-note-dump-2026-10-01/value-change-as-epistemic-update.md),
with its final-round adversarial audits. The package was driven by a staged
script — one formalizer with continuations, then four rounds of two audits and a
repair, then the gate — each stage a fresh headless agent. **Everything here is
AI-generated and has not been vetted by the author.** In these files **the
author** is the maintainer whose note is formalized.

| path | what it is |
|---|---|
| `README.md` | how to verify, the package's mechanical state, what was not shown |
| `Cleanroom/Corrigibility/CorrValueChange.lean`, `Cleanroom/Corrigibility/CorrValueChange/` | the Lean library: 22 files |
| `packages/corr-value-change/` | the report, the findings about the note, the ledger, the (empty) open list, the round-4 audits and their probe files |

## As received

| | |
|---|---|
| received | 2026-10-07 |
| archive sha256 | n/a — assembled in-repo from the run's working tree, never an archive |
| tree sha256 at intake | `a02632366b78cf51956dd94b1419d6ce0cf08ca53c635c2bfd478b3551f62bd2` (sha256 of the sorted `sha256sum` listing of every file except this one) |
| files at intake | 39 (plus ORIGIN.md) |
| generator | formalizer, auditors and repairers: Claude Fable 5.1 (Anthropic) agents; the mandate, the driver and the intake: Claude Fable 5.1 (Anthropic) in a maintainer-directed session |
| FAF pin | `159ec3f4d55948d741302a915cce388616a3875f`, the bundle's; this repository's `lean/` pins `307119d` (see `README.md`) |

## Intake deltas — what differs from the working files

- **Selection.** As for the bundle: the mandate, the first three audit rounds,
  the handoff files and the driver's logs are not included; the final audit
  round is, with its probe files. The note the package formalizes is cited in
  the corrigibility note dump beside this tree rather than copied.
- **Links.** Obsidian `[[wikilinks]]` in the package's Markdown became
  Markdown links where the target is published (the package's own files, the
  bundle's `STANDARDS.md`, the note) and code spans where it is not (the
  mandate, the earlier audit rounds, the run's audit prompt). The Lean files
  are unchanged, wikilinks in docstrings included, as in the bundle.
- **Naming.** The package's Markdown names no one. One Lean docstring
  (`Supercond.lean`, the §6.2 source line) names the author; left as it is,
  as the bundle left its Lean.
- **Local identifiers.** The clean-room declarations in the report and the
  audits name the directories the agents did not read (the earlier run's tree,
  the transcript directory) as they did in the bundle; nothing else is local.
- **Added:** `README.md` and this file.

## Not included

- **The mandate** (`corr-value-change-mandate.md`), which quotes the author's
  instruction for the run and lists the targets T1–T13, S1–S6 and E1–E5; the
  report restates every target it covers.
- **Audit rounds 1–3 and the repairs' handoff files**; the report's repair
  sections summarize each round's blocking and non-blocking issues and what was
  done about them.
- **The driver's logs.**

## Vetting status

Nothing here is vetted by the author. Nothing in this tree is registered in
this repository's claims sense. The gate is the only machine-checked content,
and it checks the Lean, not the note.

## What cites it

The note's byline in the corrigibility note dump, as refreshed on 2026-10-07.

## Checking this receipt

The tree hash is sha256 over LF-joined lines `<sha256(file)>␣␣<relative path>`,
sorted by path, excluding this file. Recompute it that way and you learn
whether the tree has moved since it arrived. Nothing enforces that it has not:
this is a receipt, not a gate. The protection that remains is that this path is
specification layer in `tests/path_gate.py`.
