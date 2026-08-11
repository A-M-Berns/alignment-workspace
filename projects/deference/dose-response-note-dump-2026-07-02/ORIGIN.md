# Origin — the dose-response note dump

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

Dose-response structure in the deference setting, with its own audit.

## As received

| | |
|---|---|
| received | 2026-07-02 |
| archive sha256 | `a69f8a9876b24dd0a2cd0b609e294c53fef0b2596c79f0037812a6a47a60e890` |
| tree sha256 at intake | `d34afa3ce288855517fb9d164adbbaa760aefe8fbf38897c130234a94ae00355` |
| files at intake | 13 |

## Third-party material

Same resolution as the note dump beside it: vendored published papers were
removed for want of redistribution rights and replaced by
`../references-citations-2026-08-11/`, which pins each by sha256.

## Scrub history

Scrubbed under the same rules on 2026-08-11 and **needed no cuts**.

## What cites it

`projects/deference/README.md`.

## Checking this receipt

The tree hash is over relative paths and file digests in sorted order, excluding
bytecode artifacts and `.DS_Store` — and **excluding this file**, which did not
exist at intake. Recompute it that way and you learn whether the tree has moved
since it arrived. Nothing enforces that it has not: this is a receipt, not a
gate. The protection that remains is that these paths are specification layer in
`tests/path_gate.py`, so a contributor cannot touch them and a maintainer's edit
is a reviewed diff in git history.
