# Lawful Φ-regret learner

**Verdict: Learning-positive, integration-blocked.**

The Blum--Mansour Theorem 18 learner is executable on the frozen eight-action,
nine-program bridge. Its sampled repository responses preserve the existing
answerability record and response-work limits. The current service model does
not price or record the learner's 72 weight updates and stationary solve, so the
full bounded-reasoner integration is not yet established.

- The [Normativity wiki](https://github.com/A-M-Berns/alignment-workspace/wiki/Normativity) is the human register.
- `PHI_REGRET_LEARNER.md` is the mathematical and implementation register.
- `ANSWERABILITY_SERVICE_AUDIT.md` records the integration boundary.
- `EXPERIMENT_RESULTS.md` contains every declared horizon, policy, and comparator.
- `THEOREM_LEDGER.md` separates source facts, tests, experiments, and open claims.
- `src/phi_learner.py` implements the row-conditioned learner and exact
  stationary selector.
- `src/experiment.py` implements fixtures, baselines, and audits.
- `tests/run.py` runs the round's checks.

Run:

```sh
python3 projects/leverage/rounds/2026-08-11-phi-regret-learner/tests/run.py
python3 projects/leverage/rounds/2026-08-11-phi-regret-learner/src/render_results.py
```

No sampled-path, high-probability, anytime, moral-truth, or comparator-coverage
theorem is claimed.
