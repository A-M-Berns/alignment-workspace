# Conventions

Carried forward from the consolidation. These are the only inherited rules; all
other freeze machinery is gone.

## Vocabulary

The retired-name gate runs over every live document in `tests/run.py`. The
canonical substitutions, ratified in the consolidation's glossary:

| use | not |
|---|---|
| incoherence | the retired word for the tolerance clause's quantity |
| downside limit | the retired word for a worldwise loss guarantee |
| core minimum, `theta_min` | the retired word, or the retired Greek letter |
| proof checker | the retired structural noun |
| settlement event | *pin*, which is reserved for settlement |
| frozen (of a digest or input) | *pinned* |
| failure pattern | the retired responsiveness-failure word |
| mechanism | the retired structural noun |

*Bound* is reserved for one-sided endorsement constraints and is not reused for
loss guarantees. A word appears in a live document only if it survives the gate;
`attic/` is retired material and is not gated.

## Status vocabulary

Any claim this tree produces, before it is consolidated, uses exactly:

- `PROVED (single derivation)`
- `MACHINE-CHECKED (stated finite scope)` — evidence for displayed finite
  instances only
- `NECESSITY WITNESS` — a displayed instance showing a named condition cannot be
  dropped; **not** a refutation of the surrounding theory
- `REFUTED (witness displayed)`
- `PROVED-CONDITIONAL (conditions listed)`
- `PROPOSED (interface revision)`

Compound forms are not used. Where a claim is both proved and machine-checked,
the status is the first and the machine check is a verification pointer.

## Footprint discipline

An objection type declares no family. It declares a **judge footprint**: the
record tables its judge may read, split into standard-supplying and evidence.
The verifier enforces the declaration — a judge reading an undeclared table has
its verdict withheld, and a judge that raises is recorded as failing rather than
passing. Families, where useful, are computed equivalence classes of footprints
and are never stored. New objection types declare a footprint over the
registered tables, a disposition, and a firing witness paired with a control.

## Evidence

Passing finite code is evidence for the displayed finite instances only.
Conditional statements list their conditions; refutations display their
witnesses; open questions are not promoted.
