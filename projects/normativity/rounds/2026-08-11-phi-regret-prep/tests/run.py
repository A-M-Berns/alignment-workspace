#!/usr/bin/env python3
"""One command: the experiment table, then the tests.

    python3 tests/run.py            run everything
    python3 tests/run.py --table    print the experiment table only

Green from this folder alone; it imports nothing outside it.
"""
from __future__ import annotations

import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src import experiments as ex  # noqa: E402
from src.regret import evaluate_class, locality  # noqa: E402


def table() -> list[str]:
    """One line per comparator: fire count, rejections, exact regret."""
    lines = [
        "| experiment | comparator | fired | first obstruction | actual | replay "
        "| regret | affordable |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for build in ex.ALL:
        experiment = build()
        report = evaluate_class(experiment.history, experiment.comparators,
                                policy=experiment.policy,
                                filings=experiment.filings)
        for outcome in report.results:
            obstruction = outcome.rejections[0][1] if outcome.rejections else "—"
            lines.append(
                f"| {experiment.label} | `{outcome.phi_id}` | {outcome.fired} "
                f"| `{obstruction}` | {outcome.actual_charge} "
                f"| {outcome.replay_charge} | {outcome.regret} "
                f"| {'yes' if outcome.admissible else 'no'} |")
    return lines


def locality_table() -> list[str]:
    """The counterfactual-influence verdict, in one place."""
    lines = [
        "| configuration | horizon | divergence | fenced bound | bound holds |",
        "|---|---|---|---|---|",
    ]
    cases = (("E9 fenced, edited account alone", ex.e9_fenced_locality),
             ("E10b fenced, one account for the run", ex.e10b_fenced_but_shared),
             ("E10c fenced, no solvency coupling", ex.e10c_no_solvency_coupling))
    for label, build in cases:
        for horizon in (12, 24):
            experiment = build(horizon=horizon)
            report = evaluate_class(experiment.history, experiment.comparators)
            outcome = report.results[0]
            check = locality(experiment.history, outcome)
            lines.append(f"| {label} | {horizon} | {abs(check.divergence)} "
                         f"| {check.bound} | {'yes' if check.holds else 'no'} |")
    for horizon in (12, 24):
        experiment = ex.e10_pooled_divergence(horizon=horizon)
        report = evaluate_class(experiment.history, experiment.comparators)
        outcome = report.results[0]
        divergence = outcome.replay_charge - outcome.actual_charge
        lines.append(f"| E10 pooled | {horizon} | {divergence} | — | not applicable |")
    return lines


def main() -> int:
    for line in table():
        print(line)
    print()
    for line in locality_table():
        print(line)
    print()
    if "--table" in sys.argv:
        return 0
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / "tests"), pattern="test_*.py",
                            top_level_dir=str(ROOT))
    runner = unittest.TextTestRunner(verbosity=2)
    return 0 if runner.run(suite).wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
