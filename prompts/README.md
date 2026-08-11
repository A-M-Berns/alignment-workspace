# Dispatch provenance

Every agent round's prompt and report live here, committed with the work they
describe. A round whose prompt is not in the tree did not happen, as far as the
repository is concerned.

## Convention

```
prompts/YYYY-MM-DD-round-name/
  PROMPT.md     the dispatch, verbatim as sent
  REPORT.md     the round's report
  <decision items>   anything the round flagged for the author
```

`YYYY-MM-DD` is the dispatch date. `round-name` is short, hyphenated, and
descriptive of the work rather than of the line — `deference-kernel`, not
`round-7`.

## Why verbatim

The prompt is kept **as sent**, including anything it got wrong. A round's report
routinely corrects its own prompt — a miscounted figure, a file that was not
where the prompt said, a decision the prompt assumed was already applied — and
those corrections are only legible against the original text. Editing a prompt
after the fact to match what happened destroys exactly the record that makes the
report checkable.

## Reports

A report states what was done, what was verified and how, what deviated from the
prompt and why, and what is awaiting the author. Where a round scored
pre-registered predictions, the scores go in the report, including the ones that
came out wrong.
