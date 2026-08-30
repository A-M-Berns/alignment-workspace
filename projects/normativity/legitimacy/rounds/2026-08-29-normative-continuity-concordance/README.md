# Normative Continuity: canonicalized checkpoint, concordance, and the Lean spine

Status: **the synthesis is `AGENT-CONSOLIDATED`; the structural theorem spine is
Lean-verified under stated abstract hypotheses; unregistered.** All names are provisional
under `AGENTS.md` §6. No claim is registered.

## Verdict

FORMALIZATION-SURVIVES — the Persistent-Wait Theorem, Persistent Opportunity, No Structural Abandonment, Grounded Replay, and their structural lemmas are proved in Lean from exactly the hypotheses the proof-pass dependency audit named, with no added assumption: Requirements 4, 5, 7, 8, 9, 10 and 12 plus finite batches for Persistent-Wait, wait responsiveness added for Persistent Opportunity, non-starvation added for No Structural Abandonment, and Requirement 1 alone for Grounded Replay, whose freshness clause is stated and never consumed. The rotating-prerequisite countermodel is Lean-verified in both directions: the ownership-only gate admits it and the Persistent-Wait conclusion fails on it, while the reach gate rejects it at the first rotation with every other requirement holding. The provenance concordance is CONCORDANT-WITH-LOCAL-REPAIRS: no theorem contradicts frozen Legitimate Evolution, and every trace the synthesis admits satisfies the frozen carry law, but successor freshness and same-batch resolution reverse decisions the frozen round recorded, the no-rewiring rule is a weakening of the Answerable Process discipline rather than a new rule, and these are recorded as errata for the next revision with the freshness reversal reserved to the author.

## What is here

| file | what it is |
|---|---|
| `NORMATIVE_CONTINUITY.tex` / `.pdf` | the checkpoint source and its render, byte-exact, digests in `ORIGIN.md` |
| `PROOF_PASS.md` | the hostile proof-pass report that marked the checkpoint |
| `src/fixtures.py` | the proof pass's executable fixtures, unchanged |
| `ORIGIN.md` | intake receipt: which of the Downloads files is the checkpoint and why, digests, status gloss |
| `CONCORDANCE.md` | provenance concordance, non-supersession map, errata, reserved decision |
| `THEOREM_MAP.md` | claims, classes, Lean names, and the dependency report |
| `tests/` | the fixtures as tests; digest check |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` | the formalization (elsewhere in the tree) |

## Status vocabulary, kept apart

- `AGENT-CONSOLIDATED` — the checkpoint's status, unchanged by this round: independently
  reconstructed, adversarially proof-checked, locally repaired, assumption-audited, and
  regression-tested by an agent.
- `CONCORDANT WITH LOCAL REPAIRS` — this round's provenance verdict, a separate fact.
- Lean-verified — exactly the results named in `THEOREM_MAP.md`, under their stated
  hypotheses. Not wait responsiveness, not non-starvation, not the scope statements, not
  adjacent work.
- Not `FROZEN`, not `CANONICAL`, not `PROVED` as a whole, not registered.

## Rerun

```sh
python3 tests/run.py                                   # fixtures and digests
cd lean && lake build Workspace.Normativity.Contrib.NormativeContinuity
```
