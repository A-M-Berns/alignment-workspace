# Origin — the deference note dump, 2026-08-11

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

The deference line's updated source corpus: everything in
`../note-dump-2026-06-27/` plus six further weeks of work — the
faithful-acceleration adjudication and its corrections, a wiki of record
(31 per-result pages with explicit status labels), the Total Trust ⟺ Value ⟺
Tower triangle closed with three direct arrows, the varying-question line, a
conjecture-attribution correction dated the day of intake, a legitimacy sketch,
two research labs, nine Lean modules, and thirteen curated conversation
transcripts. The bundle's own `README.md` carries the delta list and the
reading order; its `wiki/index.md` is the map of record.

This tree **supersedes `../note-dump-2026-06-27/` as the current state of the
source material**; the June tree remains the recorded starting point and is not
modified by this intake.

## As received

| | |
|---|---|
| received | 2026-08-11 |
| archive sha256 | `ee19de068dc01d6807b4a92318303742c53289761927e324fc49f6ff7cd203f3` |
| files in archive | 238 |
| tree sha256 at intake | `c7dabf76f67dd7c0b18350dd623d68a093311f43a1a0b9ebf412bc8187462c4f` |
| files at intake | 227 |

The intake hash is over the tree **after** the intake deltas below, which is the
state in which it enters this repository's history.

## Intake deltas — what differs from the archive

- **`references/` removed** (11 files): vendored third-party papers this
  repository has no redistribution rights to. `../references-citations-2026-08-11/`
  pins the June set by sha256. One document cited by this bundle is not covered
  by those entries and is likewise not vendored: the talk deck
  `notes/delay-program.md` calls "the deck".
- **`anson-notes/` carried in scrubbed form**: the five files that carry
  `[scrubbed]` cuts in `../note-dump-2026-06-27/` (four conversation files and
  the email-thread note) enter here as the scrubbed copies, and the navigational
  index carries the same cut applied to its newer text. The scrub history and
  its report pointer are recorded in that tree's `ORIGIN.md`; the cuts are not
  re-litigated here.
- **One duplicate payload elided**: the dose-response archive inside
  `anson-notes/`, already present as `../dose-response-note-dump-2026-07-02/`.

The bundle's `README.md` still documents `references/` as shipped; this file is
the record of the removal, matching the June tree's precedent.

## Source-side curation

The bundle was curated before it was sent. Conversation transcripts are
substance-only: tool-call bodies, session logistics and computing-infrastructure
asides removed, message numbering preserved with gaps, each file's provenance
appendix stating what was omitted, mathematics verbatim. An
infrastructure-and-identity scrub ran over the whole tree, and an independent
audit pass reviewed every file before packing. The 11 conversations under
`anson-notes/trust-between-inductors-chats/` ship raw as received, minus the
cuts above.

## Vetting status

Nearly everything dated after 2026-06-27 is unvetted by the human researcher
unless a page says otherwise, and the 2026-08-11 material is same-day. Status
labels are the bundle's own (`wiki/conventions-and-status-labels.md` — registers,
working credences, mid-chat-snapshot warnings). Nothing in this tree is
registered in this repository's claims sense.

## What cites it

Nothing at intake. `projects/deference/README.md` and `PRIORITIES.md` items 7–9
cite the June tree; whether and how they move to this one is the maintainers'
call, not this receipt's.

## Checking this receipt

The tree hash is sha256 over LF-joined lines `<sha256(file)>␣␣<relative path>`,
sorted by path, excluding bytecode artifacts, `.DS_Store` — and **this file**,
which did not exist at intake. Recompute it that way and you learn whether the
tree has moved since it arrived. Nothing enforces that it has not: this is a
receipt, not a gate. The protection that remains is that this path is
specification layer in `tests/path_gate.py`, so a contributor cannot touch it
and a maintainer's edit is a reviewed diff in git history.
