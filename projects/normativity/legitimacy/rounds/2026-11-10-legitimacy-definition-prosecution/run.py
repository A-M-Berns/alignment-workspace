#!/usr/bin/env python3
"""The round's runner.  Reads the two earlier case banks (CASE_BANK.md,
steering/CASE_BANK.md) as test material, runs the account the second follow-up tested
(teleology/), the one the third tested (decomposition/: its bank, the checks behind its
THEOREMS.md, and the facts its two addenda cite), the one the fourth tested (scored/: its bank
and the checks behind its THEOREMS.md), the setting the fifth tested (blocks/): its bank and the checks behind its
RESULTS.md, the statement the sixth tested (estimates/): its bank and the checks behind its
RESULTS.md and NEGATIVE_RESULTS.md, then the rerun of that bank under the revised definition
(rerun/): its predictions, its new scenes and the counts in its RESULTS.md.

Exit nonzero when a bank parses to nothing or holds a case twice, when an earlier case has
no prediction in either later bank, when a computed verdict diverges from its prediction
without a line in that pass's DIVERGENCES.md, or when a status in any THEOREMS.md or in
blocks/RESULTS.md or estimates/ is not the one the checks support, or when a count in
rerun/RESULTS.md is not the one computed.  `--json` prints the six reports as data."""
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
    from blocks import run as blocks
    from estimates import run as estimates
    from rerun import run as rerun
    from decomposition import bank as dbank
    from decomposition import run as current
    from scored import bank as sbank
    from scored import run as scored
    from teleology import bank as tbank
    from teleology import run as account

    banks, failures = earlier_banks()
    earlier = set(banks["first"]) | set(banks["steering"])
    for name, later in (("teleology", set(tbank.load())), ("decomposition", set(dbank.load()))):
        unpredicted = sorted(earlier - later)
        if unpredicted:
            failures.append("earlier cases with no prediction in %s/CASE_BANK.md: %s" % (name, unpredicted))
    unpredicted = sorted(set(tbank.load()) - set(dbank.load()))
    if unpredicted:
        failures.append("teleology cases with no prediction in decomposition/CASE_BANK.md: %s" % unpredicted)
    unpredicted = sorted(set(dbank.load()) - {rid if rid[-1] not in "abc" else rid[:-1] for rid in sbank.load()})
    if unpredicted:
        failures.append("decomposition cases with no prediction in scored/CASE_BANK.md: %s" % unpredicted)
    code, report = account.main()
    code2, report2 = current.main()
    code3, report3 = scored.main()
    code4, report4 = blocks.main()
    code5, report5 = estimates.main()
    code6, report6 = rerun.main()
    failures = (failures + ["teleology: " + f for f in report["failures"]]
                + ["decomposition: " + f for f in report2["failures"]] + ["scored: " + f for f in report3["failures"]]
                + ["blocks: " + f for f in report4["failures"]]
                + ["estimates: " + f for f in report5["failures"]]
                + ["rerun: " + f for f in report6["failures"]])
    if "--json" in argv:
        print(current.dumps({"teleology": report, "decomposition": report2, "scored": report3, "blocks": report4,
                             "estimates": {k: v for k, v in report5.items() if k != "tally"},
                             "rerun": {k: v for k, v in report6.items() if k != "by question"}, "failures": failures}))
    else:
        for name, rows in banks.items():
            print("%s bank: %d cases" % (name, len(rows)))
        print("\n== teleology ==")
        print(account.render(report))
        print("\n== decomposition ==")
        print(current.render(report2))
        print("\n== scored ==")
        print(scored.render(report3))
        print("\n== blocks ==")
        print(blocks.render(report4))
        print("\n== estimates ==")
        print(estimates.render(report5))
        print("\n== rerun ==")
        print(rerun.render(report6))
        print("\n" + ("OK" if not failures else "FAILURES:\n  " + "\n  ".join(failures)))
    return 1 if failures else max(code, code2, code3, code4, code5, code6)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
