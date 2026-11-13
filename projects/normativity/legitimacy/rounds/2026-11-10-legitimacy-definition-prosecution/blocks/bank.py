"""Reader for CASE_BANK.md: {case id: (title, [prediction items])}."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
HEADING = "## The table `run.py` reads"
ROW = re.compile(r"^\|\s*(\d+[abc]?)\s*\|(.*)\|\s*$")


def load():
    text = (HERE / "CASE_BANK.md").read_text(encoding="utf-8")
    if HEADING not in text:
        return {}
    rows = {}
    for line in text.split(HEADING, 1)[1].splitlines():
        m = ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in m.group(2).split("|")]
        if len(cells) != 3:
            raise SystemExit("blocks/CASE_BANK.md: row %s has %d cells, expected 4" % (m.group(1), len(cells) + 1))
        if m.group(1) in rows:
            raise SystemExit("blocks/CASE_BANK.md: case %s occurs twice" % m.group(1))
        items = [i.strip() for i in cells[2].strip("`").split(";")]
        rows[m.group(1)] = (cells[0], items)
    return rows


def matches(item, tokens):
    if item == "report":
        return True
    if item.startswith("not ") and item != "not adviser's":
        return item[4:] not in tokens
    return item in tokens
