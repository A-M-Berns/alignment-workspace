# Cleanup pass, August 10

One verification-preserving pass over the delivered package, performed before
freezing. **No mathematical content was changed, no frozen or vendored file was
touched, and no claim, status, or ledger row was edited.** This note documents
what was checked, what was found, and the two edits made. It is process
documentation, non-authoritative, and excluded from the document count it
corrects.

## Checks run

- **Every exact count in `REPORT.md` §4 recomputed** against the folder: claims
  (87, and the 50/17/12/7/1 partition consistent with the trust audit's 62
  hand-derived), Tier A source (7 modules, 2,864 lines), tests (107 = 91 Tier A
  + 16 Tier B, 1,127 lines), runner gates (7), vendored-and-frozen files (8),
  claim-ID families (runner-verified). One row was stale; see below.
- **Claim-identifier resolution outside the theory parts**: every `NL-*`
  identifier cited in the report, open problems, README, interpretation,
  for-humans, verification, corrigendum, glossary, and decision ledger resolves
  to a ledger row. All resolve.
- **Anchor uniqueness**: no duplicate `{#…}` anchors across the six theory
  parts.
- **Import locality**: every import in `src/` is standard-library or
  folder-local, confirming the README's no-sibling-tree claim.
- **Stray-marker scan**: no `TODO`/`FIXME`/`XXX`, no hardcoded absolute paths
  anywhere in code or documents (the class of problem that bit the source tree's
  rename manifest does not recur here).
- **Doubled-word scan** over all documents: clean.
- **Runner-order inspection**: the gates run in the order `VERIFICATION.md` §3
  declares, and the sorry scan is unconditional as claimed. It was, however,
  silent on success; see below.

## Edits made

1. **`REPORT.md` §4, one stale row.** The documents row read `18, 2,879 lines`;
   the folder contains 19 non-vendored documents totalling 3,032 lines. The row
   now states the recomputed numbers and excludes this note from its own count.
   No other §4 quantity was stale.
2. **`tests/run.py`, one added success line.** The unconditional sorry scan over
   vendored Lean sources printed nothing when clean, so a passing transcript
   carried no evidence the gate had fired — unlike every other gate. It now
   prints `SORRY SCAN: clean over every vendored Lean source`. No check logic
   was altered.

## Packaging

The archive is repacked without macOS resource-fork cruft (`__MACOSX/`,
`.DS_Store`). File contents are otherwise byte-identical to the delivered
package except for the two edits above and this note.

## Post-edit verification

`python3 tests/run.py` after the edits: all gates green, 107 tests pass, frozen
inputs verified, Lean skipped with the explicit message (no `MATHLIB_DIR` in the
cleanup environment). The suite transcript now shows every gate by name.

## Known items deliberately not addressed here

These are recorded elsewhere and are outside a cleanup pass's scope: the
discard-test gap for Theories 7–10 (`REPORT.md` §3 — a completing pass owes
roughly one hundred witness-row restatements); the reading-audit standing of
`NL-SI-SIM` and its corollary; and the absence of Lean coverage for the new
mathematics. Nothing in this pass changes their status.
