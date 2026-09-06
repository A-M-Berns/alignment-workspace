#!/usr/bin/env python3
"""Self-contained exact checks for this round."""

from fractions import Fraction
from pathlib import Path
import sys

ROUND = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUND))

from src.fixtures import (  # noqa: E402
    append_only_reconsideration,
    closure_admissible,
    faithful_disposal,
    hollow_disposal,
)


def main() -> None:
    faithful = faithful_disposal()
    hollow = hollow_disposal()
    assert faithful.conserved()
    assert not hollow.conserved()
    assert faithful.before_account() == frozenset({"a"})
    assert hollow.after_account() == frozenset()

    assert closure_admissible(settled=True, closes=True, prior_licence=True)
    assert not closure_admissible(settled=True, closes=False, prior_licence=True)
    assert not closure_admissible(settled=False, closes=True, prior_licence=True)
    assert not closure_admissible(settled=True, closes=True, prior_licence=False)

    reopened = append_only_reconsideration()
    assert reopened.old_token_terminal
    assert reopened.old_closure_event_present
    assert reopened.review_obligation_fresh
    assert reopened.carried_load == Fraction(1, 1)
    print("integrity constructive fixtures: PASS")


if __name__ == "__main__":
    main()
