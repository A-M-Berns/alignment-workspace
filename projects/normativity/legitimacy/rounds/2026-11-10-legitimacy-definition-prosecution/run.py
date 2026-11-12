#!/usr/bin/env python3
"""The round's runner.  Reads the two earlier case banks (CASE_BANK.md,
steering/CASE_BANK.md) as test material and exits nonzero when either parses
to nothing or a case id occurs twice."""
from __future__ import annotations

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent

BANKS = (
    ("first", "CASE_BANK.md", "## The table `run.py` reads", 5),
    ("steering", "steering/CASE_BANK.md", "## The table the runner reads", 4),
)
ROW = re.compile(r"^\|\s*([BTN]\d+)\s*\|(.*)\|\s*$")


def load_bank(rel, heading, width):
    """The rows of the table under `heading`: {case id: [cells after the id]}."""
    text = (HERE / rel).read_text(encoding="utf-8")
    if heading not in text:
        return {}
    rows = {}
    for line in text.split(heading, 1)[1].splitlines():
        m = ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", m.group(2))]
        if len(cells) != width - 1:
            raise SystemExit("%s: row %s has %d cells, expected %d" % (rel, m.group(1), len(cells) + 1, width))
        if m.group(1) in rows:
            raise SystemExit("%s: case %s occurs twice" % (rel, m.group(1)))
        rows[m.group(1)] = cells
    return rows


def earlier_banks():
    banks, failures = {}, []
    for name, rel, heading, width in BANKS:
        rows = load_bank(rel, heading, width)
        if not rows:
            failures.append("%s parsed to no cases" % rel)
        banks[name] = rows
    return banks, failures


def main(argv):
    banks, failures = earlier_banks()
    for name, rows in banks.items():
        print("%s bank: %d cases" % (name, len(rows)))
    print("OK" if not failures else "FAILURES:\n  " + "\n  ".join(failures))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
