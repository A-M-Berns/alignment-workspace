# Progress witness bridge

Status: adjacent research round extending PR69; unregistered; not frozen or settled.

## Result

The witness bridge decomposes into Persistent Relevance, Typed Witness Completeness,
and Stagnation Persistence. Typed Witness Completeness is proved in a fixed finite
service-response fragment: a reason row `v(y)-v(x)>=gamma` and complete pairwise repair
family imply robust gain `g>=gamma p(x)`. With relevant unbounded service and
nonvanishing defective response density, this derives PR69's `SW-density`; PR69 Uptake
then rules out persistent stagnation.

The service-response ontology materially expands the closed fragment to inquiry,
defeater assessment, conflict handling, and explicit revision. It still requires a
typed, licensed answer-mode comparison; a bare question or conflict does not create
one.

## Files

- `WITNESS_BRIDGE.md` — decomposition, restricted language, stagnation semantics,
  theorem, proof, composition, and dependency map.
- `SERVICE_RESPONSE_SEMANTICS.md` — action, inquiry, conflict, defeater, revision, and
  the boundary of Answer-Mode Adequacy.
- `AUTHORITY_TO_CONSTRAINTS.md` — typed compiler, conflict handling, dual receipts, and
  Operative Row Grounding from settled Grounded Replay.
- `COUNTERMODELS_2.md` — seventeen hostile traces and failed formulations.
- `REPORT.md` — final questions, exact next theorem, and verdict.
- `src/fixtures.py`, `tests/` — exact finite illustrations; not asymptotic proof.

## Run

```bash
python3 tests/run.py
```

from this directory.
