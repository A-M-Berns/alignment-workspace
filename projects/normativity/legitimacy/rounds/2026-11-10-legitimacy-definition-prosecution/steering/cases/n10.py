"""N10 — the same contents ordered by a fixed rule.  Scenario: ../CASE_BANK.md."""
from .shop import ordered


def build():
    return ordered("N10", "the same contents ordered by a fixed rule", False)
