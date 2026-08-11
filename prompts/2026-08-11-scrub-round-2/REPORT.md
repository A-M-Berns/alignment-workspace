# Scrub round 2 — report

> **Reconstructed after the fact on 2026-08-11**, from the pull-request body and
> the commit. The round's substantive report is not lost: it was written
> contemporaneously to `SCRUB_REPORT.md` at the repository root, which carries
> the per-edit table and the judgment calls. This file records what that document
> does not — the round's shape, its attribution, and its limits — and points at
> it rather than restating it.

Landed as PR #2, merged at `a63bc89`.

## What was done

Two judgment calls from the first scrub round were reversed on the maintainer's
read: two non-consenting third-party names, and nineteen bio and credential
recitals. The scrub was then widened by the maintainer's standing instruction on
personal material, which reaches further than the first round's criterion did.

36 edits in total. Beyond the reversals: five whole paragraphs on funding,
mentorship, career and morale, plus mixed passages where the personal clause came
out and the research argument stayed. `SCRUB_REPORT.md`'s round-2 section lists
each one.

Frozen digests were recomputed and `frozen/MANIFEST.md` annotated in the same
pull request, per the sanctioned procedure for moving frozen content.

## What was kept, and can be reversed

Recorded in `SCRUB_REPORT.md` rather than here. The largest standing call:
meeting-occasion framing was kept where the payload is research, and on a
stricter reading roughly a dozen further passages would come out.

## What a scrub cannot do

**Removal is at `HEAD` only.** The pre-scrub text remains in git history and is
reachable by SHA. The maintainer assessed this and accepted it; no history
rewrite was attempted.

The coverage is marker-driven — it searched for funding, mentorship, career and
morale vocabulary. A passage about the maintainer that uses none of that
vocabulary would not have surfaced. The maintainer's read-through remains the
mechanism that catches those.

## Attribution

| | |
|---|---|
| prompt author | Claude Fable 5 (Anthropic), in a maintainer-directed session |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-11 |
| this reconstruction | Claude Opus 5 (Anthropic), 2026-08-11, in the round recorded at `prompts/2026-08-11-attribution-provenance-names/` |
