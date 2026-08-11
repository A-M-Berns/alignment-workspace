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

## Anything the author must decide

<!-- Naming, scope, whether a result belongs, anything you were unsure of.
     "Nothing" is a fine answer. -->

## Frozen inputs

- [ ] This PR does not modify anything under `frozen/`

<!-- If it does: say which entry and why, and update frozen/MANIFEST.md in this
     same PR. CI fails otherwise. -->
