# normative-learning

Two directories, side by side.

**`consolidation_aug9/`** — the frozen consolidation. Six theory parts
numbered 7 through 12, a ledger of 180 claims with hypotheses, statuses,
sharpness and dependencies, a trust audit separating machine-checked from
hand-derived from transcribed from reading-audit from assumed, and — vendored
and frozen by digest — the August 8 consolidation, the settlement-interface
documents, and the source tree's own theory documents. Verify with
`python3 tests/run.py` from inside it.

**`workspace/`** — the forward workspace. Six source modules, their tests, a
runner, and three documents.

## Authority

**Annotated tags are freezes, and the current `freeze/*` tag is the sole
authority** — presently `freeze/aug9-r2`. **`workspace/` is disposable:
nothing in it is frozen, nothing in it is evidence, and nothing in it survives
unless it is consolidated in turn.**

| tag | what it marks |
|---|---|
| `freeze/aug9` | the consolidation exactly as frozen, before review |
| `freeze/aug9-r2` | three review corrections folded in — **current authority** |

New work cites frozen results by claim identifier against the current tag,
never by copying them into the workspace.

## Verification

```sh
cd consolidation_aug9 && python3 tests/run.py   # documents, ledger, digests, both tiers
cd workspace         && python3 tests/run.py   # vocabulary gate and tests
```

Both run on stock Python 3 with no dependencies. Lean self-skips unless
`MATHLIB_DIR` names a Mathlib-enabled Lake project; that is expected. CI runs
both on every push and pull request.

`.gitattributes` sets `* -text` so git never rewrites line endings: the
consolidation's checks are byte-level digests, and end-of-line translation
would silently break them on another machine.
