# Normative Continuity: the mathematical settlement

Status: **`NORMATIVE-CONTINUITY-MATH-SETTLED`; unregistered.** All names are
provisional under `AGENTS.md` §6. No claim is registered.

## Verdict

NORMATIVE-CONTINUITY-MATH-SETTLED — the structural mathematical specification, its principal modeling choices, theorem dependencies, satisfiability, and Lean theorem spine have been settled; this does not assert Coverage, Progress, substantive normative correctness, Proper Exercise, or realization by a concrete reasoner. Successor freshness is settled as the primitive because a static successor edge into an existing issue makes past opportunity depend on future records, while a route edge expresses consolidation with matter identity, reach and attention intact; same-batch opening and resolution is forbidden because every judgment about an issue reads a prefix at which it is outstanding; Due is uniformly strict-prefix; resolution is not gated by Permit; grounds are constrained only for records that change standing; Grounded Replay is stated over admitted occurrences with the live form as corollary; wait responsiveness is the primitive "no permanent no-route wait", equivalent to the eventually-met form. The paper's matter construction is proved in Lean to realize exactly the two abstract fields the theorem spine consumes, with no extra property needed, and the whole specification is inhabited in Lean and jointly satisfied by a nontrivial witness trace that exercises every departure and every red-team shape; every dependency fact of the concordance round is unchanged and the fixtures still pass.

## What is here

| file | what it is |
|---|---|
| `NORMATIVE_CONTINUITY.tex` / `.pdf` | revision 2, the settled specification; digests in `ORIGIN.md` |
| `SETTLEMENT.md` | the decisions (§1–2, 6–7), the matters realization (§3), satisfiability (§4), dependencies (§5), the membership table (§8), the red team (§9) |
| `THEOREM_MAP.md` | the Lean additions, classes, and the dependency report |
| `src/settled_model.py` | the whole specification as one checker, with witness `W` |
| `src/fixtures.py` | the proof pass's fixtures, unchanged |
| `tests/` | witness, regressions for the settled choices, digests |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §4 | matters realization, admitted Grounded Replay, primitive wait responsiveness, attention witness, inhabitant |

The `AGENT-CONSOLIDATED` checkpoint in `../2026-08-29-normative-continuity-concordance/`
is unchanged and remains the historical origin.

## Rerun

```sh
python3 tests/run.py
cd lean && lake build Workspace.Normativity.Contrib.NormativeContinuity
```
