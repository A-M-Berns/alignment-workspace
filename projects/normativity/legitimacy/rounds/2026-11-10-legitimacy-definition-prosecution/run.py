#!/usr/bin/env python3
"""The round's runner.  Reads the two earlier case banks (CASE_BANK.md,
steering/CASE_BANK.md) as test material, then runs the purpose-first account
(teleology/): its bank, and the checks behind teleology/THEOREMS.md.

Exit nonzero when a bank parses to nothing or holds a case twice, when an earlier
case has no prediction in teleology/CASE_BANK.md, when a computed verdict diverges
from its prediction without a line in teleology/DIVERGENCES.md, or when a status
in teleology/THEOREMS.md is not the one the checks support."""
from __future__ import annotations

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

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
    from teleology import bank as tbank
    from teleology import run as account

    banks, failures = earlier_banks()
    earlier = set(banks["first"]) | set(banks["steering"])
    unpredicted = sorted(earlier - set(tbank.load()))
    if unpredicted:
        failures.append("earlier cases with no prediction in teleology/CASE_BANK.md: %s" % unpredicted)
    code, report = account.main()
    report["failures"] = failures + report["failures"]
    if "--json" in argv:
        print(account.dumps(report))
    else:
        for name, rows in banks.items():
            print("%s bank: %d cases" % (name, len(rows)))
        print(account.render(report))
    return 1 if report["failures"] else code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
