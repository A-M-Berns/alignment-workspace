"""Reader for CASE_BANK.md: {case id: (title, evident, {stance: [items]})}."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
HEADING = "## The table `run.py` reads"
ROW = re.compile(r"^\|\s*([A-Z]+\d+[abc]?)\s*\|(.*)\|\s*$")
EVIDENT = ("obj", "inn", "con", "own")


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
        if len(cells) != 4:
            raise SystemExit("estimates/CASE_BANK.md: row %s has %d cells, expected 5" % (m.group(1), len(cells) + 1))
        if m.group(1) in rows:
            raise SystemExit("estimates/CASE_BANK.md: case %s occurs twice" % m.group(1))
        if cells[2] not in EVIDENT:
            raise SystemExit("estimates/CASE_BANK.md: row %s has evident character %r" % (m.group(1), cells[2]))
        parts = [p.strip() for p in cells[3].strip("`").split("//")]
        start = [i.strip() for i in parts[0].split(";")]
        end = [i.strip() for i in parts[-1].split(";")]
        rows[m.group(1)] = (cells[0], cells[2], {"start": start, "end": end})
    return rows


def matches(item, tokens):
    if item.startswith("not "):
        return item[4:] not in tokens
    return item in tokens


def standing(evident, tokens):
    """right / missed / convicted / routed / unfixed / not counted, by SETTING.md 3.12."""
    if "unfixed" in tokens:
        return "unfixed"
    if evident == "obj":
        if "manipulation" in tokens:
            return "right"
        return "missed" if "nowhere" in tokens else "routed"
    if evident == "inn":
        return "convicted" if "manipulation" in tokens else "right"
    if evident == "own":
        return "convicted" if "manipulation" in tokens else "right"
    return "not counted"
