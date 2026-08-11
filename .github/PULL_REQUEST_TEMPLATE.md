## Layer touched

- [ ] **Proof layer only** — required for non-maintainer pull requests
- [ ] Specification layer (maintainers only; `path-gate` fails otherwise)

## Claim class

<!-- lean-proved / enumeration-verified / witness-checked / test-supported /
     conjectured — or "none" if this PR adds no claim. The class is part of the
     claim; there are no silent upgrades. -->

## Statement of record

<!-- The checker id plus its exact parameters, OR the fully-qualified Lean
     declaration name. Never prose: prose documents the record, it is not the
     record. Write "none" if this PR registers no claim. -->

## OPEN_PROBLEMS item answered

<!-- The item number. Nothing enters the registry except in answer to a filed
     item; if none fits, propose one as an issue first. -->

## What this addresses

<!-- The OPEN_PROBLEMS.md item, ledger claim identifier, or issue. If none, say
     what problem this solves and why it belongs in the program. -->

## What covers it

<!-- Which tests, which Lean declarations, which witnesses. Name them; a reader
     should be able to run exactly these. -->

- [ ] `python3 tests/run.py` green locally
- [ ] Lean builds and audits clean (or: this PR touches no Lean)
- [ ] `python3 tests/check_frozen.py` green
- [ ] Exact arithmetic throughout, or floats confined to marked exploration code
- [ ] Necessity witnesses for each hypothesis, or a statement of why not feasible

## New names introduced

<!-- List every permanent-looking name this PR would establish: definitions,
     claim identifiers, file or namespace names, vocabulary. Write "none" if
     none. Contributors do not coin permanent names — mark proposals as
     provisional and the author decides. -->

none

## Provenance entries added or updated

<!-- Per AGENTS.md: each results directory carries a PROVENANCE.md declaring, per
     file or glob, its origin class (human / llm-reviewed / llm-unreviewed), the
     generator and date, the originating round under prompts/, and — if one
     exists — the originating chat bundle in frozen/. List what you added or
     changed, or write "none". -->

none

## Both documentation registers present

- [ ] Verification register (exact statements, hypotheses, how to re-verify)
- [ ] Human register (what was shown, why it matters, plain language)
- [ ] Not applicable — this PR adds no results

## Anything the author must decide

<!-- Naming, scope, whether a result belongs, anything you were unsure of.
     "Nothing" is a fine answer. -->

## Frozen inputs

- [ ] This PR does not modify anything under `frozen/`

<!-- If it does: say which entry and why, and update frozen/MANIFEST.md in this
     same PR. CI fails otherwise. -->
