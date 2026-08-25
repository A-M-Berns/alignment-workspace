# Reflective Integrity Core v1.0

Status: **specification and reference model; unregistered.** All names are
provisional under `AGENTS.md` §6. Nothing here is Lean-checked or registered.

## Verdict

FREEZE-READY — the demand interface gains the two structural properties four of the main clauses depend on, and no repair reopened the architecture.

The demand interface was the one substantive defect: `SchemaCode` carried six
structural assumptions and `DemandCode` carried none, while four of the main
clauses depend on two properties of it. `D1` (monotonicity) and `D2`
(disposition gating) close that, and with `Z3'`, `Z6` and the allocator
conditions `F1`–`F3` the four affected theorems — Episode Uniqueness, Custody
Locality, Fate Monotonicity, and the preservation form of No Invisible
Discontinuity — hold on the finite histories that previously broke them. No
store, constructor or conservation law changed.

## Contents

- `REFLECTIVE_INTEGRITY_CORE.md` — the specification, organised for
  mechanization. §34 is the dependency order; §35 is what the downstream slice
  consumes.
- `AUDIT.md` — what was repaired, from which source, and what the independent
  adversarial pass found afterwards.
- `src/ri_core.py` — reference model. Three append-only ledgers; standing,
  roots, effects, digests, fates, custody, the successor DAG and both
  conservation predicates are computed by replay.
- `src/scenarios.py` — the finite histories the specification argues about.
- `tests/` — 81 cases. `python3 tests/run.py`.

## What the tests cover

| file | fault class |
|---|---|
| `test_demand_interface.py` | D1 and D2; a non-monotone demand and an ungated demand are refused |
| `test_seed_and_episodes.py` | Z1–Z6, and Episode Uniqueness across supersession, transfer, suspension, merge, split and revocation |
| `test_freshness.py` | F1–F3, sibling and cross-time collisions, G6 domain and termination preconditions |
| `test_custody.py` | Custody Locality, Transfer, third-party disposition, repeated transfer, Digest Stability |
| `test_due_witness.py` | the biconditional swept over every scenario at every state, plus the eight-case battery |
| `test_reason_and_schema.py` | inference-step licensing separated from practical-schema semantics |
| `test_reaudit.py` | `GC ∧ AC`, trichotomy, Fate Monotonicity, TargetCoverage, Source Closure, and the independent adversarial cases |
| `test_vertical_slice.py` | write separation per step kind, and `O_t` as a projection a downstream consumer reads without writing |

## What this does not establish

`AUDIT.md` carries the full list. In short: no Lean, no registered claim, D1
and D2 decided over finite samples rather than universally, and no completeness
claim for the adversarial pass.
