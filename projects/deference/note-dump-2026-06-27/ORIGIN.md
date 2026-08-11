# Origin — the deference note dump

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

The deference line's recorded starting point: research notes across six versions,
a statement-level Lean audit, and the Lean development — deference, the
self-referential target, frozen deliberation, faithful acceleration, the tower
and acceleration results.

## As received

| | |
|---|---|
| received | 2026-06-27 |
| archive sha256 | `bc51a91b84241128380286b1a8f052a5dde01a90876dc6359cf9b6e3c9aef362` |
| tree sha256 at intake | `722b687a49a7e5f5f2ff2b8e7674fb92697d9cbf30f4f9f8b155dbb0ca48cfc1` |
| files at intake | 41 |

The intake hash above is the digest **after** the two scrub rounds below, which
is the state in which this tree entered the repository's current history.

## Third-party material — resolved 2026-08-11

This bundle vendored published third-party papers under `references/`. **This
repository has no redistribution rights to them**, so the payloads were removed
and replaced by `../references-citations-2026-08-11/`, which pins each removed
file by sha256. The record still says exactly which document the conversations
engaged with, without carrying it. Cite, do not vendor. One citation could not be
verified against a publisher of record and is flagged as unverified inside that
entry rather than reconstructed.

## Scrub history

**Round 1, 2026-08-11.** Two cuts, both candid assessments of a named person.

**Round 2, 2026-08-11.** On the maintainer's read: reversed two round-1 judgment
calls and widened the scrub to self and career material — non-consenting third
parties, bio and credential recitals, funding, mentorship-management and morale
passages. 36 edits.

All cuts are marked inline as `[scrubbed]` with no category label, because a
label leaks the thing the cut removed. `SCRUB_REPORT.md` at the repository root
lists every judgment call, including those decided in favour of keeping.

**Removal is at `HEAD` only.** The pre-scrub text remains in git history and is
reachable by SHA; the maintainer assessed this and accepted it. **The
maintainer's read-through has not happened** — the scrub is the first pass, not
the release gate.

## What cites it

`projects/deference/README.md`; `PRIORITIES.md` items 7–9.

## Checking this receipt

The tree hash is over relative paths and file digests in sorted order, excluding
bytecode artifacts and `.DS_Store` — and **excluding this file**, which did not
exist at intake. Recompute it that way and you learn whether the tree has moved
since it arrived. Nothing enforces that it has not: this is a receipt, not a
gate. The protection that remains is that these paths are specification layer in
`tests/path_gate.py`, so a contributor cannot touch them and a maintainer's edit
is a reviewed diff in git history.
