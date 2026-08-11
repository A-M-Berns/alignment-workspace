# The φ-regret preparation environment

The smallest finite substrate on which it is well defined to ask whether a
normative learner has low regret against a class of historically lawful,
reasons-responsive local edits. This round builds the environment and does not
attempt the theorem.

**Status: `ci-only`, proof layer.** Nothing here is registered in
`projects/leverage/CLAIMS.md`, and nothing here upgrades a claim of
`projects/leverage/consolidation-aug9/`, which stays authoritative for
everything it states.

## What to read, in order

| document | question it answers |
|---|---|
| `CURRENT_STATE.md` | what the leverage line holds now, and what this round could stand on |
| `REASONS_RESPONSIVENESS_INTERFACE.md` | when is an edit licensed, and which parts of that are still parameters |
| `LAWFUL_EDIT_GRAMMAR.md` | what a comparator is, and what v1 excludes |
| `REPLAY_SEMANTICS.md` | what the counterfactual run is, field by field |
| `PHI_REGRET_OBJECTIVE.md` | what is being compared, in which units, with which sign |
| `REMEDIABLE_FAILURES.md` | what self-correction would mean, stated as a conditional |
| `COUNTERFACTUAL_CHARGE_INFLUENCE.md` | how far one local edit reaches, and under what condition |
| `ONLINE_LEARNING_MAP.md` | which standard machinery is plausibly reusable |
| `PHI_REGRET_TEST_SPEC.md` | the next round's work order |
| `THEOREM_LEDGER.md` | every claim with its evidence status |
| `OPEN_PROBLEMS.md` | what this round could not settle |
| `FOR_HUMANS.md` | the same work in plain language |
| `TEST_RESULTS.md` | the numbers the runner produced |
| `COMPLETION_AUDIT.md` | what was and was not established |

## Running it

```sh
cd projects/leverage/rounds/2026-08-11-phi-regret-prep
python3 tests/run.py
```

Prints the experiment table and the locality table, then runs the suite. Exact
rationals throughout; no floats, nothing sampled, no sibling tree required.

## The one thing not to lose

Lawfulness and advantage are different questions, and the substrate keeps them
apart mechanically rather than by discipline. A certificate is checked through a
reader whose declared footprint does not contain the charge table, so an edit
cannot be licensed by what it saves even in principle: a check that reached for
the cost of an edit raises instead of returning. `tests/test_phi_regret.py`
exercises that on a guard written to do exactly that.
